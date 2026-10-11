use frontier_ecs::prelude::*;

#[derive(Clone)]
struct DamageEvent { amount: i32 }
impl Event for DamageEvent {}

#[derive(Component, Debug, Default)]
struct Health(i32);

#[derive(Component)]
struct Poisoned;

fn main() {
    let mut world = World::new();

    world.add_observer(|trigger: Trigger<OnAdd<Health>>, mut w: &mut World| {
        println!("[Observer] Entity {:?} spawned with Health!", trigger.entity);
    });

    world.add_observer(|trigger: Trigger<OnRemove<Poisoned>>, mut w: &mut World| {
        println!("[Observer] Entity {:?} is no longer poisoned!", trigger.entity);
    });

    world.add_observer(|trigger: Trigger<DamageEvent>, mut w: &mut World| {
        let entity = trigger.entity;
        let amount = trigger.event.amount;
        if let Some(mut health) = w.get_mut::<Health>(entity) {
            health.0 -= amount;
            println!("[Observer] Entity {:?} took {} damage. Health is now {}", entity, amount, health.0);
        }
    });

    let mut schedule = Schedule::new();

    fn apply_poison(mut query: Query<Entity, With<Poisoned>>, mut world: &mut World) {
        for entity in &query {
            world.trigger_targets(DamageEvent { amount: 5 }, [entity]);
        }
    }

    fn check_cure(mut query: Query<(Entity, &Health)>, mut commands: Commands) {
        for (entity, health) in &query {
            if health.0 <= 20 {
                commands.entity(entity).remove::<Poisoned>();
            }
        }
    }

    schedule.add_system(apply_poison);
    schedule.add_system(check_cure).after("apply_poison");

    let entity = world.spawn((Health(100), Poisoned));
    
    println!("--- Running Frame 1 ---");
    schedule.run(&mut world);
    
    println!("\n--- Running Frame 2 ---");
    schedule.run(&mut world);
    
    println!("\n--- Manual Event Trigger ---");
    world.trigger_targets(DamageEvent { amount: 70 }, [entity.id()]);
    world.flush_observers();

    println!("\n--- Running Frame 3 ---");
    schedule.run(&mut world);
}
