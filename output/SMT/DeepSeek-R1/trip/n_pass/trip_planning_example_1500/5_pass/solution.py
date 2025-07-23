from z3 import *

def main():
    # Define sorts
    Location = Datatype('Location')
    Location.declare('D')
    Location.declare('G')
    Location.declare('M')
    Location.declare('H')
    Location = Location.create()
    
    VehicleType = Datatype('VehicleType')
    VehicleType.declare('none')
    VehicleType.declare('truck')
    VehicleType.declare('boat')
    VehicleType = VehicleType.create()
    
    Action = Datatype('Action')
    Action.declare('NoOp')
    Action.declare('DriveTruck', ('to', Location))
    Action.declare('SailBoat', ('to', Location))
    Action.declare('LoadTruck_p1')
    Action.declare('LoadTruck_p2')
    Action.declare('UnloadTruck_p1')
    Action.declare('UnloadTruck_p2')
    Action.declare('LoadBoat_p1')
    Action.declare('LoadBoat_p2')
    Action.declare('UnloadBoat_p1')
    Action.declare('UnloadBoat_p2')
    Action = Action.create()
    
    n_steps = 7  # Number of actions, states: 0..n_steps (n_steps+1 states)
    
    # State variables
    truck_at = [Const('truck_at_%d' % i, Location) for i in range(n_steps+1)]
    boat_at = [Const('boat_at_%d' % i, Location) for i in range(n_steps+1)]
    p1_veh = [Const('p1_veh_%d' % i, VehicleType) for i in range(n_steps+1)]
    p1_loc = [Const('p1_loc_%d' % i, Location) for i in range(n_steps+1)]
    p2_veh = [Const('p2_veh_%d' % i, VehicleType) for i in range(n_steps+1)]
    p2_loc = [Const('p2_loc_%d' % i, Location) for i in range(n_steps+1)]
    
    # Action variables for each step (0 to n_steps-1)
    a = [Const('a_%d' % i, Action) for i in range(n_steps)]
    
    s = Solver()
    
    # Initial state (step 0)
    initial = And(
        truck_at[0] == Location.D,
        boat_at[0] == Location.G,
        p1_veh[0] == VehicleType.none,
        p1_loc[0] == Location.G,
        p2_veh[0] == VehicleType.none,
        p2_loc[0] == Location.M
    )
    s.add(initial)
    
    # Goal state (step n_steps)
    def effective_p1_loc(i):
        return If(p1_veh[i] == VehicleType.truck, truck_at[i],
                If(p1_veh[i] == VehicleType.boat, boat_at[i],
                p1_loc[i]))
    
    def effective_p2_loc(i):
        return If(p2_veh[i] == VehicleType.truck, truck_at[i],
                If(p2_veh[i] == VehicleType.boat, boat_at[i],
                p2_loc[i]))
    
    goal = And(
        effective_p1_loc(n_steps) == Location.H,
        effective_p2_loc(n_steps) == Location.H
    )
    s.add(goal)
    
    # Constraints for each action step
    for i in range(n_steps):
        act = a[i]
        # Frame axioms for unchanged variables
        truck_next = If(Action.is_DriveTruck(act), Action.to(act), truck_at[i])
        boat_next = If(Action.is_SailBoat(act), Action.to(act), boat_at[i])
        
        # Package1 next vehicle and location
        p1_veh_next = If(act == Action.LoadTruck_p1, VehicleType.truck,
                        If(act == Action.UnloadTruck_p1, VehicleType.none,
                        If(act == Action.LoadBoat_p1, VehicleType.boat,
                        If(act == Action.UnloadBoat_p1, VehicleType.none,
                        p1_veh[i]))))
        
        p1_loc_next = If(Or(act == Action.UnloadTruck_p1, act == Action.UnloadBoat_p1),
                        If(act == Action.UnloadTruck_p1, truck_at[i], boat_at[i]),
                        p1_loc[i])
        
        # Package2 next vehicle and location
        p2_veh_next = If(act == Action.LoadTruck_p2, VehicleType.truck,
                        If(act == Action.UnloadTruck_p2, VehicleType.none,
                        If(act == Action.LoadBoat_p2, VehicleType.boat,
                        If(act == Action.UnloadBoat_p2, VehicleType.none,
                        p2_veh[i]))))
        
        p2_loc_next = If(Or(act == Action.UnloadTruck_p2, act == Action.UnloadBoat_p2),
                        If(act == Action.UnloadTruck_p2, truck_at[i], boat_at[i]),
                        p2_loc[i])
        
        # Set next state
        s.add(truck_at[i+1] == truck_next)
        s.add(boat_at[i+1] == boat_next)
        s.add(p1_veh[i+1] == p1_veh_next)
        s.add(p1_loc[i+1] == p1_loc_next)
        s.add(p2_veh[i+1] == p2_veh_next)
        s.add(p2_loc[i+1] == p2_loc_next)
        
        # Preconditions for actions
        # DriveTruck: to must be different and in {D, G, H}
        s.add(Implies(Action.is_DriveTruck(act), 
                      And(Action.to(act) != truck_at[i],
                          Or(Action.to(act) == Location.D,
                             Action.to(act) == Location.G,
                             Action.to(act) == Location.H))))
        
        # SailBoat: to must be different and in {G, M, H}
        s.add(Implies(Action.is_SailBoat(act), 
                      And(Action.to(act) != boat_at[i],
                          Or(Action.to(act) == Location.G,
                             Action.to(act) == Location.M,
                             Action.to(act) == Location.H))))
        
        # LoadTruck_p1: package1 must be at truck location and not on vehicle
        s.add(Implies(act == Action.LoadTruck_p1, 
                      And(p1_veh[i] == VehicleType.none, 
                          p1_loc[i] == truck_at[i])))
        # LoadBoat_p1: package1 must be at boat location and not on vehicle
        s.add(Implies(act == Action.LoadBoat_p1, 
                      And(p1_veh[i] == VehicleType.none, 
                          p1_loc[i] == boat_at[i])))
        # UnloadTruck_p1: package1 must be on truck
        s.add(Implies(act == Action.UnloadTruck_p1, 
                      p1_veh[i] == VehicleType.truck))
        # UnloadBoat_p1: package1 must be on boat
        s.add(Implies(act == Action.UnloadBoat_p1, 
                      p1_veh[i] == VehicleType.boat))
        
        # Similarly for package2
        s.add(Implies(act == Action.LoadTruck_p2, 
                      And(p2_veh[i] == VehicleType.none, 
                          p2_loc[i] == truck_at[i])))
        s.add(Implies(act == Action.LoadBoat_p2, 
                      And(p2_veh[i] == VehicleType.none, 
                          p2_loc[i] == boat_at[i])))
        s.add(Implies(act == Action.UnloadTruck_p2, 
                      p2_veh[i] == VehicleType.truck))
        s.add(Implies(act == Action.UnloadBoat_p2, 
                      p2_veh[i] == VehicleType.boat))
    
    if s.check() == sat:
        m = s.model()
        plan = []
        for i in range(n_steps):
            aval = m[a[i]]
            if is_true(m.eval(Action.is_NoOp(aval))):
                plan.append('NoOp')
            elif is_true(m.eval(Action.is_DriveTruck(aval))):
                to_val = Action.to(aval)
                to_eval = m.eval(to_val)
                to_name = str(to_eval)
                plan.append(f'DriveTruck(to={to_name})')
            elif is_true(m.eval(Action.is_SailBoat(aval))):
                to_val = Action.to(aval)
                to_eval = m.eval(to_val)
                to_name = str(to_eval)
                plan.append(f'SailBoat(to={to_name})')
            elif is_true(m.eval(Action.is_LoadTruck_p1(aval))):
                plan.append('LoadTruck_p1')
            elif is_true(m.eval(Action.is_LoadTruck_p2(aval))):
                plan.append('LoadTruck_p2')
            elif is_true(m.eval(Action.is_UnloadTruck_p1(aval))):
                plan.append('UnloadTruck_p1')
            elif is_true(m.eval(Action.is_UnloadTruck_p2(aval))):
                plan.append('UnloadTruck_p2')
            elif is_true(m.eval(Action.is_LoadBoat_p1(aval))):
                plan.append('LoadBoat_p1')
            elif is_true(m.eval(Action.is_LoadBoat_p2(aval))):
                plan.append('LoadBoat_p2')
            elif is_true(m.eval(Action.is_UnloadBoat_p1(aval))):
                plan.append('UnloadBoat_p1')
            elif is_true(m.eval(Action.is_UnloadBoat_p2(aval))):
                plan.append('UnloadBoat_p2')
            else:
                plan.append(str(aval))
        print("Plan found:")
        for i, act in enumerate(plan):
            print(f"Step {i}: {act}")
    else:
        print("No plan found")

if __name__ == "__main__":
    main()