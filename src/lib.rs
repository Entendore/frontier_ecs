//! frontier-ecs v0.6.0 — Observers & Event-Driven Architecture
//!
//! Upgrades:
//! - Replaced `ComponentHooks` with fully reactive `Observers`.
//! - `OnAdd<T>`, `OnInsert<T>`, `OnRemove<T>` are now triggerable Events.
//! - Custom user events via `world.trigger(Event)` and `world.trigger_targets(Event, entities)`.
//! - Recursive observer queue processing for cascading structural changes.

use std::alloc::{alloc, dealloc, Layout};
use std::any::{Any, TypeId};
use std::cell::UnsafeCell;
use std::collections::{HashMap, VecDeque};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::panic::AssertUnwindSafe;
use std::ptr;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Mutex;

// ============================================================================
// Core: Entity, Components, Archetypes & Graph
// ============================================================================

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Entity(u64);

impl Entity {
    pub const PLACEHOLDER: Entity = Entity(u64::MAX);
    #[inline] pub const fn from_raw(id: u32, gen: u32) -> Self { Self(((gen as u64) << 32) | id as u64) }
    #[inline] pub const fn index(self) -> u32 { self.0 as u32 }
    #[inline] pub const fn generation(self) -> u32 { (self.0 >> 32) as u32 }
}

pub type ComponentId = u32;
pub type ArchetypeId = u32;

pub trait Component: 'static + Send + Sync {}
impl<T: 'static + Send + Sync> Component for T {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StorageType { Table, SparseSet }

struct ComponentInfo {
    id: ComponentId, type_id: TypeId, name: &'static str,
    size: usize, align: usize, storage: StorageType,
    drop_fn: unsafe fn(*mut u8, usize),
    trigger_remove_fn: unsafe fn(&mut World, Entity),
}

unsafe fn drop_slice<T>(ptr: *mut u8, len: usize) {
    if size_of::<T>() != 0 { ptr::drop_in_place(std::slice::from_raw_parts_mut(ptr as *mut T, len)); }
}

unsafe fn trigger_remove<T: Component>(world: &mut World, entity: Entity) {
    world.trigger_targets(OnRemove::<T>, [entity]);
}

pub struct Components {
    infos: Vec<ComponentInfo>,
    by_type: HashMap<TypeId, ComponentId>,
}

impl Components {
    pub fn new() -> Self { Self { infos: Vec::new(), by_type: HashMap::new() } }
    pub fn register<T: Component>(&mut self) -> ComponentId {
        self.register_with_storage::<T>(StorageType::Table)
    }
    pub fn register_with_storage<T: Component>(&mut self, storage: StorageType) -> ComponentId {
        if let Some(&id) = self.by_type.get(&TypeId::of::<T>()) { return id; }
        let id = self.infos.len() as ComponentId;
        self.infos.push(ComponentInfo {
            id, type_id: TypeId::of::<T>(), name: std::any::type_name::<T>(),
            size: size_of::<T>(), align: align_of::<T>(), storage, drop_fn: drop_slice::<T>,
            trigger_remove_fn: trigger_remove::<T>,
        });
        self.by_type.insert(TypeId::of::<T>(), id);
        id
    }
    #[inline] pub fn get_id<T: Component>(&self) -> Option<ComponentId> { self.by_type.get(&TypeId::of::<T>()).copied() }
    #[inline] pub fn info(&self, id: ComponentId) -> &ComponentInfo { &self.infos[id as usize] }
    #[inline] pub fn storage(&self, id: ComponentId) -> StorageType { self.infos[id as usize].storage }
}

#[derive(Clone, Copy, Debug)]
pub struct EntityLocation { pub archetype_id: ArchetypeId, pub row: u32 }
impl EntityLocation {
    pub const INVALID: Self = Self { archetype_id: u32::MAX, row: u32::MAX };
}

pub struct ComponentColumn {
    component_id: ComponentId, data: *mut u8, capacity: usize, len: usize,
    element_size: usize, element_align: usize, drop_fn: unsafe fn(*mut u8, usize),
    ticks_added: Vec<u32>, ticks_changed: Vec<u32>,
}
unsafe impl Send for ComponentColumn {} unsafe impl Sync for ComponentColumn {}

impl ComponentColumn {
    fn new(info: &ComponentInfo) -> Self {
        Self {
            component_id: info.id, data: ptr::null_mut(), capacity: 0, len: 0,
            element_size: info.size.max(1), element_align: info.align.max(1),
            drop_fn: info.drop_fn, ticks_added: Vec::new(), ticks_changed: Vec::new(),
        }
    }
    #[inline] pub unsafe fn ptr_at(&self, row: usize) -> *mut u8 { self.data.add(row * self.element_size) }
    #[inline] pub unsafe fn get_ptr(&self, row: usize) -> *const u8 { self.ptr_at(row) }

    fn reserve(&mut self, additional: usize) {
        let needed = self.len + additional;
        if needed <= self.capacity { return; }
        let new_cap = (self.capacity * 2).max(needed).max(16);
        unsafe {
            let nl = Layout::from_size_align_unchecked(new_cap * self.element_size, self.element_align);
            let nd = if self.data.is_null() { alloc(nl) } else {
                let ol = Layout::from_size_align_unchecked(self.capacity * self.element_size, self.element_align);
                let p = alloc(nl);
                ptr::copy_nonoverlapping(self.data, p, self.len * self.element_size);
                dealloc(self.data, ol); p
            };
            self.data = nd;
        }
        self.capacity = new_cap;
    }

    pub unsafe fn write(&mut self, row: usize, value: *const u8, tick: u32) {
        debug_assert!(row < self.len);
        ptr::copy_nonoverlapping(value, self.ptr_at(row), self.element_size);
        self.ticks_changed[row] = tick;
    }

    fn push_uninit(&mut self, tick: u32) -> usize {
        self.reserve(1);
        let row = self.len;
        self.ticks_added.push(tick);
        self.ticks_changed.push(tick);
        self.len += 1;
        row
    }

    pub fn mark_changed(&mut self, row: usize, tick: u32) {
        if row < self.ticks_changed.len() { self.ticks_changed[row] = tick; }
    }
    #[inline] pub fn tick_added(&self, row: usize) -> u32 { self.ticks_added[row] }
    #[inline] pub fn tick_changed(&self, row: usize) -> u32 { self.ticks_changed[row] }

    unsafe fn swap_remove(&mut self, row: usize) {
        let last = self.len - 1;
        if row != last {
            ptr::copy_nonoverlapping(self.ptr_at(last), self.ptr_at(row), self.element_size);
            self.ticks_added[row] = self.ticks_added[last];
            self.ticks_changed[row] = self.ticks_changed[last];
        }
        (self.drop_fn)(self.ptr_at(last), 1);
        self.ticks_added.pop();
        self.ticks_changed.pop();
        self.len -= 1;
    }
}

impl Drop for ComponentColumn {
    fn drop(&mut self) {
        unsafe {
            if !self.data.is_null() {
                if self.len > 0 { (self.drop_fn)(self.data, self.len); }
                if self.capacity > 0 {
                    let l = Layout::from_size_align_unchecked(self.capacity * self.element_size, self.element_align);
                    dealloc(self.data, l);
                }
            }
        }
    }
}

pub struct Archetype {
    id: ArchetypeId,
    component_ids: Vec<ComponentId>,
    columns: Vec<ComponentColumn>,
    column_index: HashMap<ComponentId, usize>,
    entities: Vec<Entity>,
    len: usize,
    add_edges: HashMap<ComponentId, ArchetypeId>,
    remove_edges: HashMap<ComponentId, ArchetypeId>,
}
unsafe impl Send for Archetype {} unsafe impl Sync for Archetype {}

impl Archetype {
    fn new(id: ArchetypeId, components: &Components, ids: Vec<ComponentId>) -> Self {
        let mut columns = Vec::with_capacity(ids.len());
        let mut column_index = HashMap::new();
        for &cid in &ids {
            column_index.insert(cid, columns.len());
            columns.push(ComponentColumn::new(components.info(cid)));
        }
        Self { id, component_ids: ids, columns, column_index, entities: Vec::new(), len: 0, add_edges: HashMap::new(), remove_edges: HashMap::new() }
    }
    #[inline] pub fn id(&self) -> ArchetypeId { self.id }
    #[inline] pub fn len(&self) -> usize { self.len }
    #[inline] pub fn component_ids(&self) -> &[ComponentId] { &self.component_ids }
    #[inline] pub fn has(&self, cid: ComponentId) -> bool { self.column_index.contains_key(&cid) }
    #[inline] pub fn column(&self, cid: ComponentId) -> Option<&ComponentColumn> { self.column_index.get(&cid).map(|&i| &self.columns[i]) }
    #[inline] pub fn column_mut(&mut self, cid: ComponentId) -> Option<&mut ComponentColumn> { self.column_index.get(&cid).map(move |&i| &mut self.columns[i]) }
    #[inline] pub fn entities(&self) -> &[Entity] { &self.entities }

    fn allocate_row(&mut self, entity: Entity, tick: u32) -> u32 {
        let row = self.len;
        self.entities.push(entity);
        for col in &mut self.columns { col.push_uninit(tick); }
        self.len += 1;
        row as u32
    }

    pub unsafe fn write_component(&mut self, cid: ComponentId, row: u32, value: *const u8, tick: u32) {
        if let Some(&i) = self.column_index.get(&cid) { self.columns[i].write(row as usize, value, tick); }
    }

    unsafe fn swap_remove_row(&mut self, row: u32) -> Option<Entity> {
        let last = self.len - 1;
        let moved = if row as usize != last {
            for col in &mut self.columns {
                ptr::copy_nonoverlapping(col.ptr_at(last), col.ptr_at(row as usize), col.element_size);
                col.ticks_added[row as usize] = col.ticks_added[last];
                col.ticks_changed[row as usize] = col.ticks_changed[last];
            }
            self.entities[row as usize] = self.entities[last];
            Some(self.entities[row as usize])
        } else { None };
        for col in &mut self.columns {
            (col.drop_fn)(col.ptr_at(last), 1);
            col.ticks_added.pop();
            col.ticks_changed.pop();
            col.len -= 1;
        }
        self.entities.pop();
        self.len -= 1;
        moved
    }
}

pub struct Archetypes {
    archetypes: Vec<Archetype>,
    by_components: HashMap<Vec<ComponentId>, ArchetypeId>,
    generation: u32,
}
impl Archetypes {
    pub fn new() -> Self { Self { archetypes: Vec::new(), by_components: HashMap::new(), generation: 0 } }
    
    pub fn get_or_create(&mut self, components: &Components, mut ids: Vec<ComponentId>) -> ArchetypeId {
        ids.sort_unstable();
        if let Some(&id) = self.by_components.get(&ids) { return id; }
        let id = self.archetypes.len() as ArchetypeId;
        self.archetypes.push(Archetype::new(id, components, ids.clone()));
        self.by_components.insert(ids, id);
        self.generation += 1;
        id
    }
    
    pub fn get_or_create_add_edge(&mut self, components: &Components, src: ArchetypeId, cid: ComponentId) -> ArchetypeId {
        if let Some(&target) = self.archetypes[src as usize].add_edges.get(&cid) { return target; }
        let mut new_ids = self.archetypes[src as usize].component_ids.clone();
        new_ids.push(cid);
        let target = self.get_or_create(components, new_ids);
        self.archetypes[src as usize].add_edges.insert(cid, target);
        self.archetypes[target as usize].remove_edges.insert(cid, src);
        target
    }
    
    pub fn get_or_create_remove_edge(&mut self, components: &Components, src: ArchetypeId, cid: ComponentId) -> ArchetypeId {
        if let Some(&target) = self.archetypes[src as usize].remove_edges.get(&cid) { return target; }
        let src_ids = self.archetypes[src as usize].component_ids.clone();
        let new_ids: Vec<_> = src_ids.into_iter().filter(|&c| c != cid).collect();
        let target = self.get_or_create(components, new_ids);
        self.archetypes[src as usize].remove_edges.insert(cid, target);
        self.archetypes[target as usize].add_edges.insert(cid, src);
        target
    }

    #[inline] pub fn get(&self, id: ArchetypeId) -> &Archetype { &self.archetypes[id as usize] }
    #[inline] pub fn get_mut(&mut self, id: ArchetypeId) -> &mut Archetype { &mut self.archetypes[id as usize] }
    pub fn iter(&self) -> impl Iterator<Item = &Archetype> { self.archetypes.iter() }
    pub fn len(&self) -> usize { self.archetypes.len() }
    pub fn generation(&self) -> u32 { self.generation }
}

// ============================================================================
// Events, Observers, and Triggers
// ============================================================================

pub trait Event: 'static + Send + Sync + Clone {}
impl<T: 'static + Send + Sync + Clone> Event for T {}

// Lifecycle Events
pub struct OnAdd<T: Component>(PhantomData<T>);
impl<T: Component> Clone for OnAdd<T> { fn clone(&self) -> Self { Self(PhantomData) } }
impl<T: Component> Event for OnAdd<T> {}

pub struct OnInsert<T: Component>(PhantomData<T>);
impl<T: Component> Clone for OnInsert<T> { fn clone(&self) -> Self { Self(PhantomData) } }
impl<T: Component> Event for OnInsert<T> {}

pub struct OnRemove<T: Component>(PhantomData<T>);
impl<T: Component> Clone for OnRemove<T> { fn clone(&self) -> Self { Self(PhantomData) } }
impl<T: Component> Event for OnRemove<T> {}

pub struct Trigger<'a, E: Event> {
    pub event: &'a E,
    pub entity: Entity,
}

type ObserverErased = Box<dyn FnMut(&mut World, &dyn Any, Entity) + Send + Sync>;

pub struct Observers {
    map: HashMap<TypeId, Vec<ObserverErased>>,
}

impl Observers {
    pub fn new() -> Self { Self { map: HashMap::new() } }
    
    pub fn add<E: Event, F>(&mut self, observer: F)
    where
        F: FnMut(Trigger<E>, &mut World) + Send + Sync + 'static,
    {
        let mut observer = observer;
        let boxed: ObserverErased = Box::new(move |world, data, entity| {
            let event = data.downcast_ref::<E>().expect("Observer event type mismatch");
            observer(Trigger { event, entity }, world);
        });
        self.map.entry(TypeId::of::<E>()).or_default().push(boxed);
    }

    pub fn get_mut(&mut self, type_id: TypeId) -> Option<&mut Vec<ObserverErased>> {
        self.map.get_mut(&type_id)
    }
}

struct PendingTrigger {
    type_id: TypeId,
    data: Box<dyn Any + Send + Sync>,
    entity: Entity,
}

// ============================================================================
// SparseSet, Entities, Bundles, Resources
// ============================================================================

pub struct SparseSet { sparse: Vec<Option<u32>>, dense: Vec<Entity>, data: *mut u8, cap: usize, len: usize, element_size: usize, element_align: usize, drop_fn: unsafe fn(*mut u8, usize), ticks_added: Vec<u32>, ticks_changed: Vec<u32> }
unsafe impl Send for SparseSet {} unsafe impl Sync for SparseSet {}
impl SparseSet {
    fn new(info: &ComponentInfo) -> Self { Self { sparse: Vec::new(), dense: Vec::new(), data: ptr::null_mut(), cap: 0, len: 0, element_size: info.size.max(1), element_align: info.align.max(1), drop_fn: info.drop_fn, ticks_added: Vec::new(), ticks_changed: Vec::new() } }
    pub fn contains(&self, e: Entity) -> bool { self.sparse.get(e.index() as usize).map_or(false, |o| o.is_some()) }
    pub fn get(&self, e: Entity) -> Option<*const u8> { let d = *self.sparse.get(e.index() as usize)?.as_ref()?; unsafe { Some(self.data.add(d as usize * self.element_size)) } }
    pub fn insert(&mut self, e: Entity, value: *const u8, tick: u32) {
        let idx = e.index() as usize;
        if idx >= self.sparse.len() { self.sparse.resize(idx + 1, None); }
        if let Some(d) = self.sparse[idx] { unsafe { ptr::copy_nonoverlapping(value, self.data.add(d as usize * self.element_size), self.element_size); } self.ticks_changed[d as usize] = tick; return; }
        let needed = self.len + 1; let new_cap = (self.cap * 2).max(needed).max(16);
        unsafe { let nl = Layout::from_size_align_unchecked(new_cap * self.element_size, self.element_align); let nd = if self.data.is_null() { std::alloc::alloc(nl) } else { let ol = Layout::from_size_align_unchecked(self.cap * self.element_size, self.element_align); let p = std::alloc::alloc(nl); ptr::copy_nonoverlapping(self.data, p, self.len * self.element_size); std::alloc::dealloc(self.data, ol); p }; self.data = nd; } self.cap = new_cap;
        let d = self.len as u32; unsafe { ptr::copy_nonoverlapping(value, self.data.add(self.len * self.element_size), self.element_size); }
        self.dense.push(e); self.ticks_added.push(tick); self.ticks_changed.push(tick); self.sparse[idx] = Some(d); self.len += 1;
    }
}
impl Drop for SparseSet { fn drop(&mut self) { unsafe { if !self.data.is_null() { if self.len > 0 { (self.drop_fn)(self.data, self.len); } if self.cap > 0 { let l = Layout::from_size_align_unchecked(self.cap * self.element_size, self.element_align); std::alloc::dealloc(self.data, l); } } } } }

pub struct Entities { meta: Vec<EntityMeta>, free: Vec<u32> }
struct EntityMeta { generation: u32, location: EntityLocation, alive: bool }
impl Entities {
    pub fn new() -> Self { Self { meta: Vec::new(), free: Vec::new() } }
    pub fn reserve(&mut self) -> Entity {
        if let Some(id) = self.free.pop() {
            let g = self.meta[id as usize].generation + 1;
            self.meta[id as usize] = EntityMeta { generation: g, location: EntityLocation::INVALID, alive: true };
            Entity::from_raw(id, g)
        } else {
            let id = self.meta.len() as u32;
            self.meta.push(EntityMeta { generation: 0, location: EntityLocation::INVALID, alive: true });
            Entity::from_raw(id, 0)
        }
    }
    pub fn alloc(&mut self, loc: EntityLocation) -> Entity {
        let e = self.reserve();
        self.set_location(e, loc);
        e
    }
    pub fn free(&mut self, e: Entity) {
        if let Some(m) = self.meta.get_mut(e.index() as usize) {
            if m.generation == e.generation() && m.alive { m.alive = false; self.free.push(e.index()); }
        }
    }
    pub fn location(&self, e: Entity) -> Option<EntityLocation> {
        let m = self.meta.get(e.index() as usize)?;
        (m.generation == e.generation() && m.alive).then_some(m.location)
    }
    pub fn set_location(&mut self, e: Entity, loc: EntityLocation) {
        if let Some(m) = self.meta.get_mut(e.index() as usize) {
            if m.generation == e.generation() && m.alive { m.location = loc; }
        }
    }
    pub fn contains(&self, e: Entity) -> bool {
        self.meta.get(e.index() as usize).map_or(false, |m| m.generation == e.generation() && m.alive)
    }
}

pub trait Bundle: Send + Sync + 'static {
    fn component_ids(components: &mut Components) -> Vec<ComponentId>;
    fn components(&self, components: &Components) -> Vec<(ComponentId, *const u8)>;
    fn trigger_on_add(world: &mut World, entity: Entity);
    fn trigger_on_insert(world: &mut World, entity: Entity);
}

macro_rules! impl_bundle_tuple {
    ($($T:ident),*) => {
        impl<$($T: Component),*> Bundle for ($($T,)*) {
            fn component_ids(c: &mut Components) -> Vec<ComponentId> { vec![$(c.register::<$T>()),*] }
            fn components(&self, c: &Components) -> Vec<(ComponentId, *const u8)> {
                #[allow(non_snake_case)] let ($($T,)*) = self;
                vec![$((c.get_id::<$T>().unwrap(), $T as *const $T as *const u8)),*]
            }
            fn trigger_on_add(world: &mut World, entity: Entity) {
                $(world.trigger_targets(OnAdd::<$T>, [entity]);)*
            }
            fn trigger_on_insert(world: &mut World, entity: Entity) {
                $(world.trigger_targets(OnInsert::<$T>, [entity]);)*
            }
        }
    };
}
impl_bundle_tuple!(); impl_bundle_tuple!(A); impl_bundle_tuple!(A, B); impl_bundle_tuple!(A, B, C); impl_bundle_tuple!(A, B, C, D); impl_bundle_tuple!(A, B, C, D, E); impl_bundle_tuple!(A, B, C, D, E, F);

pub trait Resource: 'static + Send + Sync {}
impl<T: 'static + Send + Sync> Resource for T {}

pub struct Resources { data: HashMap<TypeId, Box<dyn Any + Send + Sync>>, ticks: HashMap<TypeId, u32>, added_ticks: HashMap<TypeId, u32> }
impl Resources {
    pub fn new() -> Self { Self { data: HashMap::new(), ticks: HashMap::new(), added_ticks: HashMap::new() } }
    pub fn insert<T: Resource>(&mut self, value: T, tick: u32) {
        let id = TypeId::of::<T>(); let was = self.data.contains_key(&id);
        self.data.insert(id, Box::new(value)); self.ticks.insert(id, tick);
        if !was { self.added_ticks.insert(id, tick); }
    }
    pub fn get<T: Resource>(&self) -> Option<&T> { self.data.get(&TypeId::of::<T>()).and_then(|b| b.downcast_ref::<T>()) }
    pub fn get_mut<T: Resource>(&mut self, tick: u32) -> Option<&mut T> {
        let id = TypeId::of::<T>(); self.ticks.insert(id, tick);
        self.data.get_mut(&id).and_then(|b| b.downcast_mut::<T>())
    }
    pub fn contains<T: Resource>(&self) -> bool { self.data.contains_key(&TypeId::of::<T>()) }
}

// ============================================================================
// Commands (Fully Deferred, Parallel Safe)
// ============================================================================

type Command = Box<dyn FnOnce(&mut World) + Send>;

pub struct Commands<'w> {
    world: &'w UnsafeCell<World>,
    queue: &'w mut Vec<Command>,
}
unsafe impl<'w> Send for Commands<'w> {}

impl<'w> Commands<'w> {
    pub fn spawn<B: Bundle>(&mut self, bundle: B) -> EntityCommands<'_> {
        let entity = unsafe { (*self.world.get()).entities.reserve() };
        let boxed = Box::new(bundle);
        let ptr = Box::into_raw(boxed);
        let _ = B::component_ids(unsafe { &mut (*self.world.get()).components });
        let drop_fn: Command = Box::new(move |w: &mut World| {
            let b = unsafe { Box::from_raw(ptr) }; 
            w.spawn_inner(entity, b);
        });
        self.queue.push(drop_fn);
        EntityCommands { entity, commands: self }
    }

    pub fn entity(&mut self, entity: Entity) -> EntityCommands<'_> {
        EntityCommands { entity, commands: self }
    }

    pub fn despawn(&mut self, entity: Entity) -> &mut Self {
        let cmd: Command = Box::new(move |w: &mut World| { w.despawn(entity); });
        self.queue.push(cmd); self
    }

    pub fn insert_resource<T: Resource>(&mut self, value: T) -> &mut Self {
        let cmd: Command = Box::new(move |w: &mut World| {
            let tick = unsafe { (*w.inner.get()).change_tick.load(Ordering::Acquire) };
            unsafe { &mut *w.inner.get() }.resources.insert(value, tick);
        });
        self.queue.push(cmd); self
    }
}

pub struct EntityCommands<'a, 'w> {
    entity: Entity,
    commands: &'a mut Commands<'w>,
}

impl<'a, 'w> EntityCommands<'a, 'w> {
    pub fn id(&self) -> Entity { self.entity }
    
    pub fn insert<B: Bundle>(&mut self, bundle: B) -> &mut Self {
        let boxed = Box::new(bundle);
        let ptr = Box::into_raw(boxed);
        let _ = B::component_ids(unsafe { &mut (*self.commands.world.get()).components });
        let entity = self.entity;
        let drop_fn: Command = Box::new(move |w: &mut World| {
            let b = unsafe { Box::from_raw(ptr) }; w.insert_inner(entity, b);
        });
        self.commands.queue.push(drop_fn);
        self
    }

    pub fn remove<T: Component>(&mut self) -> &mut Self {
        let entity = self.entity;
        let cmd: Command = Box::new(move |w: &mut World| { w.remove::<T>(entity); });
        self.commands.queue.push(cmd);
        self
    }

    pub fn despawn(&mut self) -> &mut Self {
        self.commands.despawn(self.entity);
        self
    }
}

// ============================================================================
// Access & WorldQuery
// ============================================================================

#[derive(Default, Clone)]
pub struct Access {
    component_reads: Vec<ComponentId>, component_writes: Vec<ComponentId>,
    resource_reads: Vec<TypeId>, resource_writes: Vec<TypeId>,
    archetype_mutates: bool,
}
impl Access {
    pub fn add_read(&mut self, cid: ComponentId) { self.component_reads.push(cid); }
    pub fn add_write(&mut self, cid: ComponentId) { self.component_writes.push(cid); }
    pub fn add_resource_read(&mut self, t: TypeId) { self.resource_reads.push(t); }
    pub fn add_resource_write(&mut self, t: TypeId) { self.resource_writes.push(t); }
    pub fn set_mutates(&mut self) { self.archetype_mutates = true; }
    pub fn conflicts(&self, other: &Access) -> bool {
        if self.archetype_mutates || other.archetype_mutates {
            return !self.component_writes.is_empty() || !other.component_writes.is_empty()
                || !self.component_reads.is_empty() || !other.component_reads.is_empty()
                || self.archetype_mutates && other.archetype_mutates;
        }
        for &w in &self.component_writes {
            if other.component_writes.contains(&w) || other.component_reads.contains(&w) { return true; }
        }
        for &r in &self.component_reads {
            if other.component_writes.contains(&r) { return true; }
        }
        for &w in &self.resource_writes {
            if other.resource_writes.contains(&w) || other.resource_reads.contains(&w) { return true; }
        }
        for &r in &self.resource_reads {
            if other.resource_writes.contains(&r) { return true; }
        }
        false
    }
}

pub trait WorldQuery {
    type Item<'a>;
    type State: Send + Sync;
    fn init_state(world: &mut World) -> Self::State;
    fn update_access(state: &Self::State, access: &mut Access);
    fn matches(state: &Self::State, archetype: &Archetype) -> bool;
    unsafe fn fetch<'a>(archetype: &'a Archetype, row: usize, state: &Self::State) -> Self::Item<'a>;
}

pub trait ReadOnlyQuery: WorldQuery {}

impl<T: Component> WorldQuery for &T {
    type Item<'a> = &'a T; type State = ComponentId;
    fn init_state(world: &mut World) -> Self::State { world.components.register::<T>() }
    fn update_access(s: &Self::State, a: &mut Access) { a.component_reads.push(*s); }
    fn matches(s: &Self::State, arch: &Archetype) -> bool { arch.has(*s) }
    unsafe fn fetch<'a>(arch: &'a Archetype, row: usize, s: &Self::State) -> &'a T {
        let col = arch.column(*s).unwrap(); &*(col.get_ptr(row) as *const T)
    }
}
impl<T: Component> ReadOnlyQuery for &T {}

impl<T: Component> WorldQuery for &mut T {
    type Item<'a> = &'a mut T; type State = ComponentId;
    fn init_state(world: &mut World) -> Self::State { world.components.register::<T>() }
    fn update_access(s: &Self::State, a: &mut Access) { a.component_writes.push(*s); }
    fn matches(s: &Self::State, arch: &Archetype) -> bool { arch.has(*s) }
    unsafe fn fetch<'a>(arch: &'a Archetype, row: usize, s: &Self::State) -> &'a mut T {
        let col = arch.column(*s).unwrap(); &mut *(col.get_ptr(row) as *mut T)
    }
}

impl<T: Component> WorldQuery for Option<&T> {
    type Item<'a> = Option<&'a T>; type State = ComponentId;
    fn init_state(world: &mut World) -> Self::State { world.components.register::<T>() }
    fn update_access(s: &Self::State, a: &mut Access) { a.component_reads.push(*s); }
    fn matches(_s: &Self::State, _arch: &Archetype) -> bool { true }
    unsafe fn fetch<'a>(arch: &'a Archetype, row: usize, s: &Self::State) -> Option<&'a T> {
        arch.column(*s).map(|col| &*(col.get_ptr(row) as *const T))
    }
}
impl<T: Component> ReadOnlyQuery for Option<&T> {}

impl<T: Component> WorldQuery for Option<&mut T> {
    type Item<'a> = Option<&'a mut T>; type State = ComponentId;
    fn init_state(world: &mut World) -> Self::State { world.components.register::<T>() }
    fn update_access(s: &Self::State, a: &mut Access) { a.component_writes.push(*s); }
    fn matches(_s: &Self::State, _arch: &Archetype) -> bool { true }
    unsafe fn fetch<'a>(arch: &'a Archetype, row: usize, s: &Self::State) -> Option<&'a mut T> {
        arch.column(*s).map(|col| &mut *(col.get_ptr(row) as *mut T))
    }
}

impl WorldQuery for Entity {
    type Item<'a> = Entity; type State = ();
    fn init_state(_w: &mut World) -> Self::State { () }
    fn update_access(_s: &Self::State, _a: &mut Access) {}
    fn matches(_s: &Self::State, _arch: &Archetype) -> bool { true }
    unsafe fn fetch<'a>(arch: &'a Archetype, row: usize, _s: &Self::State) -> Entity { arch.entities[row] }
}
impl ReadOnlyQuery for Entity {}

macro_rules! impl_wq_tuple {
    ($($T:ident),*) => {
        impl<$($T: WorldQuery),*> WorldQuery for ($($T,)*) {
            type Item<'a> = ($($T::Item<'a>,)*); type State = ($($T::State,)*);
            fn init_state(world: &mut World) -> Self::State { ($($T::init_state(world),)*) }
            fn update_access(state: &Self::State, access: &mut Access) {
                #[allow(non_snake_case)] let ($($T,)*) = state; $($T::update_access($T, access);)*
            }
            fn matches(state: &Self::State, arch: &Archetype) -> bool {
                #[allow(non_snake_case)] let ($($T,)*) = state; $($T::matches($T, arch))&&*
            }
            unsafe fn fetch<'a>(arch: &'a Archetype, row: usize, state: &Self::State) -> Self::Item<'a> {
                #[allow(non_snake_case)] let ($($T,)*) = state; ($($T::fetch(arch, row, $T),)*)
            }
        }
        impl<$($T: ReadOnlyQuery),*> ReadOnlyQuery for ($($T,)*) {}
    };
}
impl_wq_tuple!(); impl_wq_tuple!(A); impl_wq_tuple!(A, B); impl_wq_tuple!(A, B, C); impl_wq_tuple!(A, B, C, D); impl_wq_tuple!(A, B, C, D, E); impl_wq_tuple!(A, B, C, D, E, F);

// ============================================================================
// Query State & Iteration
// ============================================================================

pub trait QueryFilter {
    type State: Send + Sync;
    fn init_state(world: &mut World) -> Self::State;
    fn update_access(state: &Self::State, access: &mut Access);
    fn matches(state: &Self::State, arch: &Archetype, row: usize, last_run: u32, this_run: u32) -> bool;
}

impl QueryFilter for () {
    type State = (); fn init_state(_: &mut World) -> Self::State { () }
    fn update_access(_: &Self::State, _: &mut Access) {}
    fn matches(_: &Self::State, _: &Archetype, _: usize, _: u32, _: u32) -> bool { true }
}

pub struct Added<T>(PhantomData<T>);
impl<T: Component> QueryFilter for Added<T> {
    type State = ComponentId; fn init_state(w: &mut World) -> Self::State { w.components.register::<T>() }
    fn update_access(s: &Self::State, a: &mut Access) { a.component_reads.push(*s); }
    fn matches(s: &Self::State, arch: &Archetype, row: usize, last_run: u32, _: u32) -> bool {
        arch.column(*s).map_or(false, |c| c.tick_added(row) > last_run)
    }
}

pub struct Changed<T>(PhantomData<T>);
impl<T: Component> QueryFilter for Changed<T> {
    type State = ComponentId; fn init_state(w: &mut World) -> Self::State { w.components.register::<T>() }
    fn update_access(s: &Self::State, a: &mut Access) { a.component_reads.push(*s); }
    fn matches(s: &Self::State, arch: &Archetype, row: usize, last_run: u32, _: u32) -> bool {
        arch.column(*s).map_or(false, |c| c.tick_changed(row) > last_run)
    }
}

pub struct With<T>(PhantomData<T>);
impl<T: Component> QueryFilter for With<T> {
    type State = ComponentId; fn init_state(w: &mut World) -> Self::State { w.components.register::<T>() }
    fn update_access(s: &Self::State, a: &mut Access) { a.component_reads.push(*s); }
    fn matches(s: &Self::State, arch: &Archetype, _: usize, _: u32, _: u32) -> bool { arch.has(*s) }
}

macro_rules! impl_filter_tuple {
    ($($T:ident),*) => {
        impl<$($T: QueryFilter),*> QueryFilter for ($($T,)*) {
            type State = ($($T::State,)*); fn init_state(w: &mut World) -> Self::State { ($($T::init_state(w),)*) }
            fn update_access(s: &Self::State, a: &mut Access) { #[allow(non_snake_case)] let ($($T,)*) = s; $($T::update_access($T, a);)* }
            fn matches(s: &Self::State, arch: &Archetype, row: usize, lr: u32, tr: u32) -> bool { #[allow(non_snake_case)] let ($($T,)*) = s; $($T::matches($T, arch, row, lr, tr))&&* }
        }
    };
}
impl_filter_tuple!(); impl_filter_tuple!(A); impl_filter_tuple!(A, B); impl_filter_tuple!(A, B, C); impl_filter_tuple!(A, B, C, D);

pub struct QueryState<Q: WorldQuery, F: QueryFilter = ()> {
    q: Q::State, f: F::State,
    last_run: u32, this_run: u32,
    matched_archetypes: Vec<ArchetypeId>,
    archetype_generation: u32,
}

pub struct Query<'w, Q: WorldQuery, F: QueryFilter = ()> {
    world: &'w World,
    state: &'w QueryState<Q, F>,
    _marker: PhantomData<(&'w Q, &'w F)>,
}

impl<'w, Q: WorldQuery, F: QueryFilter> Query<'w, Q, F> {
    pub fn iter(&self) -> QueryIter<'_, 'w, Q, F> {
        QueryIter { world: self.world, state: self.state, arch_idx: 0, row: 0, _marker: PhantomData }
    }
    pub fn iter_mut(&mut self) -> QueryIter<'_, 'w, Q, F> { self.iter() }

    pub fn get(&self, entity: Entity) -> Option<Q::Item<'_>> {
        let inner = unsafe { &*self.world.inner.get() };
        let loc = inner.entities.location(entity)?;
        if loc.archetype_id == u32::MAX { return None; }
        let arch = inner.archetypes.get(loc.archetype_id);
        if !Q::matches(&self.state.q, arch) { return None; }
        if !F::matches(&self.state.f, arch, loc.row as usize, self.state.last_run, self.state.this_run) { return None; }
        unsafe { Some(Q::fetch(arch, loc.row as usize, &self.state.q)) }
    }

    pub fn for_each<FN: FnMut(Q::Item<'_>)>(&self, mut f: FN) {
        let inner = unsafe { &*self.world.inner.get() };
        for &arch_id in &self.state.matched_archetypes {
            let arch = inner.archetypes.get(arch_id);
            for row in 0..arch.len() {
                if F::matches(&self.state.f, arch, row, self.state.last_run, self.state.this_run) {
                    let item = unsafe { Q::fetch(arch, row, &self.state.q) };
                    f(item);
                }
            }
        }
    }

    pub fn par_iter(&self) -> QueryParIter<'_, 'w, Q, F> {
        QueryParIter { query: self, batch_size: 1024 }
    }
}

pub struct QueryIter<'a, 'w, Q: WorldQuery, F: QueryFilter> {
    world: &'a World, state: &'a QueryState<Q, F>, arch_idx: usize, row: usize, _marker: PhantomData<&'w ()>,
}
impl<'a, 'w, Q: WorldQuery, F: QueryFilter> Iterator for QueryIter<'a, 'w, Q, F> {
    type Item = Q::Item<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.arch_idx >= self.state.matched_archetypes.len() { return None; }
            let arch_id = self.state.matched_archetypes[self.arch_idx];
            let arch = unsafe { &*self.world.inner.get() }.archetypes.get(arch_id);
            if self.row >= arch.len() {
                self.arch_idx += 1; self.row = 0; continue;
            }
            let row = self.row;
            self.row += 1;
            if F::matches(&self.state.f, arch, row, self.state.last_run, self.state.this_run) {
                return unsafe { Some(Q::fetch(arch, row, &self.state.q)) };
            }
        }
    }
}

pub struct QueryParIter<'a, 'w, Q: WorldQuery, F: QueryFilter> {
    query: &'a Query<'w, Q, F>,
    batch_size: usize,
}
impl<'a, 'w, Q: WorldQuery, F: QueryFilter> QueryParIter<'a, 'w, Q, F> {
    pub fn batch_size(mut self, size: usize) -> Self { self.batch_size = size.max(1); self }
    pub fn for_each<FN>(&self, f: FN)
    where
        FN: Fn(Q::Item<'_>) + Send + Sync,
        for<'b> Q::Item<'b>: Send,
    {
        let batch = self.batch_size;
        let inner = unsafe { &*self.query.world.inner.get() };
        let q_state = self.query.state;
        std::thread::scope(|s| {
            for &arch_id in &q_state.matched_archetypes {
                let arch = inner.archetypes.get(arch_id);
                let len = arch.len();
                let chunks = len.div_ceil(batch);
                for chunk_idx in 0..chunks {
                    let start = chunk_idx * batch;
                    let end = ((chunk_idx + 1) * batch).min(len);
                    let f_ref = &f;
                    s.spawn(move || {
                        for row in start..end {
                            if F::matches(&q_state.f, arch, row, q_state.last_run, q_state.this_run) {
                                let item = unsafe { Q::fetch(arch, row, &q_state.q) };
                                f_ref(item);
                            }
                        }
                    });
                }
            }
        });
    }
}

// ============================================================================
// World & SystemParam
// ============================================================================

pub struct World { pub(crate) inner: UnsafeCell<WorldInner> }
unsafe impl Sync for World {}

pub(crate) struct WorldInner {
    pub entities: Entities,
    pub archetypes: Archetypes,
    pub components: Components,
    pub sparse_sets: HashMap<ComponentId, SparseSet>,
    pub resources: Resources,
    pub observers: Observers,
    pub pending_triggers: VecDeque<PendingTrigger>,
    pub change_tick: AtomicU32,
    pub last_change_tick: u32,
}

impl World {
    pub fn new() -> Self {
        let mut inner = WorldInner {
            entities: Entities::new(), archetypes: Archetypes::new(), components: Components::new(),
            sparse_sets: HashMap::new(), resources: Resources::new(), observers: Observers::new(),
            pending_triggers: VecDeque::new(), change_tick: AtomicU32::new(1), last_change_tick: 0,
        };
        inner.archetypes.get_or_create(&inner.components, Vec::new());
        Self { inner: UnsafeCell::new(inner) }
    }

    pub fn add_observer<E: Event, F>(&mut self, observer: F)
    where
        F: FnMut(Trigger<E>, &mut World) + Send + Sync + 'static,
    {
        unsafe { &mut *self.inner.get() }.observers.add::<E, F>(observer);
    }

    pub fn trigger<E: Event>(&mut self, event: E) {
        self.trigger_targets(event, [Entity::PLACEHOLDER]);
    }

    pub fn trigger_targets<E: Event>(&mut self, event: E, targets: impl IntoIterator<Item = Entity>) {
        let inner = unsafe { &mut *self.inner.get() };
        let type_id = TypeId::of::<E>();
        for entity in targets {
            inner.pending_triggers.push_back(PendingTrigger {
                type_id,
                data: Box::new(event.clone()),
                entity,
            });
        }
    }

    pub fn flush_observers(&mut self) {
        loop {
            let inner = unsafe { &mut *self.inner.get() };
            let Some(trigger) = inner.pending_triggers.pop_front() else { break; };
            let type_id = trigger.type_id;
            let entity = trigger.entity;
            
            let Some(observers) = inner.observers.get_mut(type_id) else { continue; };
            drop(inner); // Release borrow
            
            for observer in observers {
                let world_ref = unsafe { &mut *(self.inner.get() as *mut World) };
                observer(world_ref, trigger.data.as_ref(), entity);
            }
        }
    }

    pub fn spawn<B: Bundle>(&mut self, bundle: B) -> EntityMut<'_> {
        let entity = unsafe { &mut *self.inner.get() }.entities.reserve();
        self.spawn_inner(entity, bundle);
        EntityMut { world: self, entity }
    }
    
    pub(crate) fn spawn_inner<B: Bundle>(&mut self, entity: Entity, bundle: B) {
        let inner = unsafe { &mut *self.inner.get() };
        let mut ids = B::component_ids(&mut inner.components);
        ids.sort_unstable();
        let tick = inner.change_tick.load(Ordering::Acquire);
        let arch_id = inner.archetypes.get_or_create(&inner.components, ids.clone());
        let arch = inner.archetypes.get_mut(arch_id);
        let row = arch.allocate_row(entity, tick);
        
        let pairs = bundle.components(&inner.components);
        for (cid, ptr) in &pairs {
            if inner.components.storage(*cid) == StorageType::Table {
                unsafe { arch.write_component(*cid, row, *ptr, tick); }
            }
        }
        inner.entities.set_location(entity, EntityLocation { archetype_id: arch_id, row });
        
        drop(inner);
        B::trigger_on_add(self, entity);
        B::trigger_on_insert(self, entity);
    }

    pub fn insert<B: Bundle>(&mut self, entity: Entity, bundle: B) -> bool { self.insert_inner(entity, bundle) }
    pub(crate) fn insert_inner<B: Bundle>(&mut self, entity: Entity, bundle: B) -> bool {
        let inner = unsafe { &mut *self.inner.get() };
        let Some(loc) = inner.entities.location(entity) else { return false; };
        let new_ids = B::component_ids(&mut inner.components);
        let tick = inner.change_tick.load(Ordering::Acquire);
        
        let mut current_arch = loc.archetype_id;
        for &cid in &new_ids {
            current_arch = inner.archetypes.get_or_create_add_edge(&inner.components, current_arch, cid);
        }
        
        let new_arch_id = current_arch;
        unsafe {
            let old_arch = inner.archetypes.get(loc.archetype_id);
            let new_arch = inner.archetypes.get_mut(new_arch_id);
            let new_row = new_arch.allocate_row(entity, tick);
            
            for &cid in old_arch.component_ids() {
                if let Some(col) = old_arch.column(cid) {
                    let src = col.get_ptr(loc.row as usize);
                    new_arch.write_component(cid, new_row, src, tick);
                }
            }
            
            let pairs = bundle.components(&inner.components);
            for (cid, ptr) in &pairs {
                if inner.components.storage(*cid) == StorageType::Table {
                    new_arch.write_component(*cid, new_row, *ptr, tick);
                }
            }
            
            let old_arch = inner.archetypes.get_mut(loc.archetype_id);
            let moved = old_arch.swap_remove_row(loc.row);
            if let Some(m) = moved {
                inner.entities.set_location(m, EntityLocation { archetype_id: loc.archetype_id, row: loc.row });
            }
            inner.entities.set_location(entity, EntityLocation { archetype_id: new_arch_id, row: new_row });
        }
        drop(inner);
        B::trigger_on_insert(self, entity);
        true
    }

    pub fn remove<T: Component>(&mut self, entity: Entity) -> Option<T> {
        let inner = unsafe { &mut *self.inner.get() };
        let loc = inner.entities.location(entity)?;
        let cid = inner.components.register::<T>();
        if !inner.archetypes.get(loc.archetype_id).has(cid) { return None; }
        
        self.trigger_targets(OnRemove::<T>, [entity]);
        self.flush_observers();
        
        let new_arch_id = inner.archetypes.get_or_create_remove_edge(&inner.components, loc.archetype_id, cid);
        let tick = inner.change_tick.load(Ordering::Acquire);
        
        unsafe {
            let old_arch = inner.archetypes.get(loc.archetype_id);
            let new_arch = inner.archetypes.get_mut(new_arch_id);
            let new_row = new_arch.allocate_row(entity, tick);
            let mut taken = std::mem::MaybeUninit::<T>::uninit();
            
            for &c in old_arch.component_ids() {
                if c == cid {
                    let p = old_arch.column(c).unwrap().get_ptr(loc.row as usize);
                    ptr::copy_nonoverlapping(p, taken.as_mut_ptr() as *mut u8, std::mem::size_of::<T>());
                } else if let Some(col) = old_arch.column(c) {
                    new_arch.write_component(c, new_row, col.get_ptr(loc.row as usize), tick);
                }
            }
            
            let old_arch = inner.archetypes.get_mut(loc.archetype_id);
            let moved = old_arch.swap_remove_row(loc.row);
            if let Some(m) = moved {
                inner.entities.set_location(m, EntityLocation { archetype_id: loc.archetype_id, row: loc.row });
            }
            inner.entities.set_location(entity, EntityLocation { archetype_id: new_arch_id, row: new_row });
            Some(taken.assume_init())
        }
    }

    pub fn despawn(&mut self, entity: Entity) -> bool { 
        let inner = unsafe { &mut *self.inner.get() };
        let Some(loc) = inner.entities.location(entity) else { return false; };

        let trigger_fns: Vec<_> = inner.archetypes.get(loc.archetype_id).component_ids().iter()
            .map(|&cid| inner.components.info(cid).trigger_remove_fn)
            .collect();
        drop(inner);
        
        for f in trigger_fns {
            f(self, entity);
        }
        self.flush_observers();

        let inner = unsafe { &mut *self.inner.get() };
        unsafe {
            let arch = inner.archetypes.get_mut(loc.archetype_id);
            let moved = arch.swap_remove_row(loc.row);
            if let Some(m) = moved { inner.entities.set_location(m, EntityLocation { archetype_id: loc.archetype_id, row: loc.row }); }
        }
        inner.entities.free(entity); true
    }
    
    pub fn get<T: Component>(&self, entity: Entity) -> Option<&T> {
        let inner = unsafe { &*self.inner.get() };
        let loc = inner.entities.location(entity)?;
        let cid = inner.components.get_id::<T>()?;
        let arch = inner.archetypes.get(loc.archetype_id);
        if let Some(col) = arch.column(cid) {
            unsafe { Some(&*(col.get_ptr(loc.row as usize) as *const T)) }
        } else { None }
    }

    pub fn get_mut<T: Component>(&mut self, entity: Entity) -> Option<&mut T> {
        let inner = unsafe { &mut *self.inner.get() };
        let loc = inner.entities.location(entity)?;
        let cid = inner.components.get_id::<T>()?;
        let tick = inner.change_tick.load(Ordering::Acquire);
        let arch = inner.archetypes.get_mut(loc.archetype_id);
        if let Some(col) = arch.column_mut(cid) {
            col.mark_changed(loc.row as usize, tick);
            unsafe { Some(&mut *(col.get_ptr(loc.row as usize) as *mut T)) }
        } else { None }
    }

    pub fn entity_mut(&mut self, entity: Entity) -> Option<EntityMut<'_>> {
        if unsafe { &*self.inner.get() }.entities.contains(entity) {
            Some(EntityMut { world: self, entity })
        } else {
            None
        }
    }

    pub fn insert_resource<T: Resource>(&mut self, value: T) {
        let inner = unsafe { &mut *self.inner.get() };
        let tick = inner.change_tick.load(Ordering::Acquire);
        inner.resources.insert(value, tick);
    }
    pub fn resource<T: Resource>(&self) -> Option<&T> { unsafe { &*self.inner.get() }.resources.get::<T>() }
    pub fn resource_mut<T: Resource>(&mut self) -> Option<&mut T> {
        let inner = unsafe { &mut *self.inner.get() };
        let tick = inner.change_tick.load(Ordering::Acquire);
        inner.resources.get_mut::<T>(tick)
    }
    
    pub fn cell(&self) -> WorldCell<'_> { WorldCell { world: &self.inner } }
    pub fn change_tick(&self) -> u32 { unsafe { (*self.inner.get()).change_tick.load(Ordering::Acquire) } }
    pub fn increment_change_tick(&self) { unsafe { (*self.inner.get()).change_tick.fetch_add(1, Ordering::Release); } }
    pub(crate) fn archetypes(&self) -> &Archetypes { unsafe { &*self.inner.get() }.archetypes() }
}

pub struct EntityMut<'w> {
    world: &'w mut World,
    entity: Entity,
}

impl<'w> EntityMut<'w> {
    pub fn id(&self) -> Entity { self.entity }
    pub fn insert<B: Bundle>(&mut self, bundle: B) -> &mut Self {
        self.world.insert(self.entity, bundle);
        self
    }
    pub fn remove<T: Component>(&mut self) -> &mut Self {
        self.world.remove::<T>(self.entity);
        self
    }
    pub fn despawn(&mut self) {
        self.world.despawn(self.entity);
    }
    pub fn get<T: Component>(&self) -> Option<&T> {
        self.world.get::<T>(self.entity)
    }
    pub fn get_mut<T: Component>(&mut self) -> Option<&mut T> {
        self.world.get_mut::<T>(self.entity)
    }
}

impl WorldInner {
    pub(crate) fn archetypes(&self) -> &Archetypes { &self.archetypes }
}

pub struct WorldCell<'w> { world: &'w UnsafeCell<WorldInner> }
unsafe impl<'w> Sync for WorldCell<'w> {}
unsafe impl<'w> Send for WorldCell<'w> {}
impl<'w> WorldCell<'w> {
    #[inline] pub unsafe fn get(&self) -> &WorldInner { &*self.world.get() }
    #[inline] pub unsafe fn get_mut(&self) -> &mut WorldInner { &mut *self.world.get() }
}

pub trait SystemParam {
    type Item<'w>;
    type State: Send + Sync;
    fn init_state(world: &mut World, access: &mut Access) -> Self::State;
    unsafe fn fetch<'w>(world: WorldCell<'w>, state: &'w mut Self::State) -> Self::Item<'w>;
    fn update_archetype_state(state: &mut Self::State, world: &World);
    fn drain_commands(state: &mut Self::State) -> Vec<Command> { Vec::new() }
}

impl<'x, Q: WorldQuery, F: QueryFilter> SystemParam for Query<'x, Q, F> {
    type Item<'w> = Query<'w, Q, F>;
    type State = QueryState<Q, F>;
    fn init_state(world: &mut World, access: &mut Access) -> Self::State {
        let q = Q::init_state(world); let f = F::init_state(world);
        Q::update_access(&q, access); F::update_access(&f, access);
        QueryState { q, f, last_run: 0, this_run: 0, matched_archetypes: Vec::new(), archetype_generation: 0 }
    }
    unsafe fn fetch<'w>(world: WorldCell<'w>, state: &'w mut Self::State) -> Query<'w, Q, F> {
        let inner = world.get();
        state.last_run = inner.last_change_tick;
        state.this_run = inner.change_tick.load(Ordering::Acquire);
        Query { world: &*(world.world as *const _ as *const World), state: &*(&*state as *const _), _marker: PhantomData }
    }
    fn update_archetype_state(state: &mut Self::State, world: &World) {
        let inner = unsafe { &*world.inner.get() };
        if state.archetype_generation != inner.archetypes.generation() {
            state.matched_archetypes.clear();
            for arch in inner.archetypes.iter() {
                if Q::matches(&state.q, arch) { state.matched_archetypes.push(arch.id()); }
            }
            state.archetype_generation = inner.archetypes.generation();
        }
    }
}

pub struct Res<'w, T: Resource> { value: &'w T, last_run: u32, this_run: u32 }
impl<'w, T: Resource> Deref for Res<'w, T> { type Target = T; fn deref(&self) -> &T { self.value } }
impl<T: Resource> SystemParam for Res<'_, T> {
    type Item<'w> = Res<'w, T>; type State = ();
    fn init_state(_w: &mut World, access: &mut Access) -> Self::State { access.add_resource_read(TypeId::of::<T>()); () }
    unsafe fn fetch<'w>(world: WorldCell<'w>, _state: &'w mut Self::State) -> Res<'w, T> {
        let inner = world.get(); Res { value: inner.resources.get::<T>().unwrap(), last_run: inner.last_change_tick, this_run: inner.change_tick.load(Ordering::Acquire) }
    }
    fn update_archetype_state(_state: &mut Self::State, _world: &World) {}
}

pub struct ResMut<'w, T: Resource> { value: &'w mut T, last_run: u32, this_run: u32 }
impl<'w, T: Resource> Deref for ResMut<'w, T> { type Target = T; fn deref(&self) -> &T { self.value } }
impl<'w, T: Resource> DerefMut for ResMut<'w, T> { fn deref_mut(&mut self) -> &mut T { self.value } }
impl<T: Resource> SystemParam for ResMut<'_, T> {
    type Item<'w> = ResMut<'w, T>; type State = ();
    fn init_state(_w: &mut World, access: &mut Access) -> Self::State { access.add_resource_write(TypeId::of::<T>()); () }
    unsafe fn fetch<'w>(world: WorldCell<'w>, _state: &'w mut Self::State) -> ResMut<'w, T> {
        let inner = world.get_mut(); let tick = inner.change_tick.load(Ordering::Acquire);
        ResMut { value: inner.resources.get_mut::<T>(tick).unwrap(), last_run: inner.last_change_tick, this_run: tick }
    }
    fn update_archetype_state(_state: &mut Self::State, _world: &World) {}
}

pub struct CommandsState { queue: Vec<Command> }
impl<'x> SystemParam for Commands<'x> {
    type Item<'w> = Commands<'w>; 
    type State = CommandsState;
    fn init_state(_w: &mut World, _access: &mut Access) -> Self::State { 
        CommandsState { queue: Vec::new() } 
    }
    unsafe fn fetch<'w>(world: WorldCell<'w>, state: &'w mut Self::State) -> Commands<'w> {
        Commands { world: world.world, queue: &mut state.queue }
    }
    fn update_archetype_state(_state: &mut Self::State, _world: &World) {}
    fn drain_commands(state: &mut Self::State) -> Vec<Command> {
        std::mem::take(&mut state.queue)
    }
}

macro_rules! impl_sp_tuple {
    ($($T:ident),*) => {
        impl<$($T: SystemParam),*> SystemParam for ($($T,)*) {
            type Item<'w> = ($($T::Item<'w>,)*); type State = ($($T::State,)*);
            fn init_state(world: &mut World, access: &mut Access) -> Self::State { ($($T::init_state(world, access),)*) }
            unsafe fn fetch<'w>(world: WorldCell<'w>, state: &'w mut Self::State) -> Self::Item<'w> {
                #[allow(non_snake_case)] let ($($T,)*) = state; ($($T::fetch(world, $T),)*)
            }
            fn update_archetype_state(state: &mut Self::State, world: &World) {
                #[allow(non_snake_case)] let ($($T,)*) = state; $($T::update_archetype_state($T, world);)*
            }
            fn drain_commands(state: &mut Self::State) -> Vec<Command> {
                #[allow(non_snake_case)] let ($($T,)*) = state;
                let mut cmds = Vec::new();
                $(cmds.extend($T::drain_commands($T));)*
                cmds
            }
        }
    };
}
impl_sp_tuple!(); impl_sp_tuple!(A); impl_sp_tuple!(A, B); impl_sp_tuple!(A, B, C); impl_sp_tuple!(A, B, C, D); impl_sp_tuple!(A, B, C, D, E); impl_sp_tuple!(A, B, C, D, E, F);

pub trait System: Send + Sync {
    fn name(&self) -> &str;
    fn access(&self) -> &Access;
    fn init(&mut self, world: &mut World);
    fn update_archetype_state(&mut self, world: &World);
    fn run(&mut self, world: WorldCell<'_>);
    fn drain_commands(&mut self) -> Vec<Command> { Vec::new() }
}

pub struct FunctionSystem<F, Params: SystemParam> {
    func: F, state: Option<Params::State>, access: Access, name: &'static str, _marker: PhantomData<Params>,
}

impl<F, Params: SystemParam> System for FunctionSystem<F, Params>
where F: for<'w> Fn(Params::Item<'w>) + Send + Sync + 'static {
    fn name(&self) -> &str { self.name }
    fn access(&self) -> &Access { &self.access }
    fn init(&mut self, world: &mut World) {
        let mut access = Access::default();
        let state = Params::init_state(world, &mut access);
        self.state = Some(state); self.access = access;
    }
    fn update_archetype_state(&mut self, world: &World) {
        if let Some(state) = self.state.as_mut() { Params::update_archetype_state(state, world); }
    }
    fn run(&mut self, world: WorldCell<'_>) {
        let state = self.state.as_mut().expect("System not initialized");
        let item = unsafe { Params::fetch(world, state) };
        (self.func)(item);
    }
    fn drain_commands(&mut self) -> Vec<Command> {
        if let Some(state) = self.state.as_mut() { Params::drain_commands(state) } else { Vec::new() }
    }
}

pub trait IntoSystem<Marker> { type System: System; fn into_system(self) -> Self::System; }

macro_rules! impl_into_system {
    ($($T:ident),*) => {
        impl<F, $($T: SystemParam),*> IntoSystem<fn($($T,)*)> for F
        where F: for<'w> Fn($($T::Item<'w>),*) + Send + Sync + 'static {
            type System = FunctionSystem<F, ($($T,)*)>;
            fn into_system(self) -> Self::System {
                FunctionSystem { func: self, state: None, access: Access::default(), name: std::any::type_name::<F>(), _marker: PhantomData }
            }
        }
    };
}
impl_into_system!(A); impl_into_system!(A, B); impl_into_system!(A, B, C); impl_into_system!(A, B, C, D); impl_into_system!(A, B, C, D, E); impl_into_system!(A, B, C, D, E, F);

pub struct ExclusiveSystem<F> { func: F, name: &'static str, access: Access }
impl<F: Fn(&mut World) + Send + Sync + 'static> System for ExclusiveSystem<F> {
    fn name(&self) -> &str { self.name }
    fn access(&self) -> &Access { &self.access }
    fn init(&mut self, _world: &mut World) { self.access = Access::default(); self.access.set_mutates(); }
    fn update_archetype_state(&mut self, _world: &World) {}
    fn run(&mut self, world: WorldCell<'_>) {
        let world_ref = unsafe { &mut *(world.world as *mut WorldInner as *mut World) };
        (self.func)(world_ref);
    }
}
impl<F: Fn(&mut World) + Send + Sync + 'static> IntoSystem<fn(&mut World)> for F {
    type System = ExclusiveSystem<F>;
    fn into_system(self) -> Self::System { ExclusiveSystem { func: self, name: std::any::type_name::<F>(), access: Access::default() } }
}

// ============================================================================
// Schedule (With Panic Catching & Conditions)
// ============================================================================

pub struct SystemDescriptor {
    system: Box<dyn System>,
    name: String,
    in_sets: Vec<String>,
    before: Vec<String>,
    after: Vec<String>,
    conditions: Vec<Box<dyn Fn(&World) -> bool + Send + Sync>>,
}

impl SystemDescriptor {
    pub fn in_set(mut self, set: &str) -> Self { self.in_sets.push(set.to_string()); self }
    pub fn before(mut self, name: &str) -> Self { self.before.push(name.to_string()); self }
    pub fn after(mut self, name: &str) -> Self { self.after.push(name.to_string()); self }
    pub fn run_if(mut self, condition: impl Fn(&World) -> bool + Send + Sync + 'static) -> Self {
        self.conditions.push(Box::new(condition));
        self
    }
}

pub struct Schedule {
    descriptors: Vec<SystemDescriptor>,
    initialized: bool,
    command_queue: Vec<Command>,
}

impl Schedule {
    pub fn new() -> Self { Self { descriptors: Vec::new(), initialized: false, command_queue: Vec::new() } }

    pub fn add_system<S: IntoSystem<M>, M>(&mut self, system: S) -> &mut SystemDescriptor {
        let s = system.into_system();
        let name = s.name().to_string();
        self.descriptors.push(SystemDescriptor { system: Box::new(s), name: name.clone(), in_sets: Vec::new(), before: Vec::new(), after: Vec::new(), conditions: Vec::new() });
        self.descriptors.last_mut().unwrap()
    }

    pub fn run(&mut self, world: &mut World) {
        if !self.initialized {
            for d in &mut self.descriptors { d.system.init(world); }
            self.initialized = true;
        }
        for d in &mut self.descriptors { d.system.update_archetype_state(world); }

        let mut sorted_indices = Vec::new();
        let mut visited = vec![false; self.descriptors.len()];
        fn visit(idx: usize, descs: &[SystemDescriptor], visited: &mut [bool], sorted: &mut Vec<usize>) {
            if visited[idx] { return; }
            visited[idx] = true;
            for after_name in &descs[idx].after {
                if let Some(i) = descs.iter().position(|d| &d.name == after_name || d.in_sets.iter().any(|s| s == after_name)) {
                    visit(i, descs, visited, sorted);
                }
            }
            sorted.push(idx);
        }
        for i in 0..self.descriptors.len() { visit(i, &self.descriptors, &mut visited, &mut sorted_indices); }

        let mut stages: Vec<Vec<usize>> = Vec::new();
        for &idx in &sorted_indices {
            let access = self.descriptors[idx].system.access();
            let mut placed = false;
            for stage in &mut stages {
                if !stage.iter().any(|&j| self.descriptors[j].system.access().conflicts(access)) {
                    stage.push(idx); placed = true; break;
                }
            }
            if !placed { stages.push(vec![idx]); }
        }

        let world_cell = world.cell();
        for stage in stages {
            let active_systems: Vec<usize> = stage.into_iter().filter(|&idx| {
                self.descriptors[idx].conditions.iter().all(|c| c(world))
            }).collect();
            
            if active_systems.is_empty() { continue; }
            
            if active_systems.len() == 1 {
                let idx = active_systems[0];
                let sys = &mut self.descriptors[idx].system;
                let name = sys.name().to_string();
                
                let res = std::panic::catch_unwind(AssertUnwindSafe(|| {
                    sys.run(world_cell);
                }));
                if let Err(e) = res {
                    eprintln!("[ECS] System '{}' panicked: {:?}", name, e);
                }
            } else {
                std::thread::scope(|s| {
                    let ptr = self.descriptors.as_mut_ptr();
                    for &idx in &active_systems {
                        let sys = unsafe { &mut *ptr.add(idx) };
                        let name = sys.system.name().to_string();
                        s.spawn(move || {
                            let res = std::panic::catch_unwind(AssertUnwindSafe(|| {
                                sys.system.run(world_cell);
                            }));
                            if let Err(e) = res {
                                eprintln!("[ECS] System '{}' panicked: {:?}", name, e);
                            }
                        });
                    }
                });
            }
            
            for &idx in &active_systems {
                let cmds = self.descriptors[idx].system.drain_commands();
                self.command_queue.extend(cmds);
            }
            
            let inner = unsafe { &mut *world.inner.get() };
            let queue = std::mem::take(&mut self.command_queue);
            drop(inner);
            for cmd in queue { cmd(world); }
            
            world.flush_observers();
        }
        
        let inner = unsafe { &mut *world.inner.get() };
        inner.last_change_tick = world.change_tick();
        world.increment_change_tick();
    }
}

pub mod prelude {
    pub use crate::*;
}
