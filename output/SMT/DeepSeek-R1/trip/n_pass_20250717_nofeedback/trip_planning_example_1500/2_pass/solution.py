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
        # Frame axioms for unchanged variables: we set next state to current state by default, then override for changes.
        # Truck next location
        truck_next = If(act.is_DriveTruck(), act.to, truck_at[i])
        # Boat next location
        boat_next = If(act.is_SailBoat(), act.to, boat_at[i])
        
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
        # DriveTruck: to must be different from current location
        s.add(Implies(act.is_DriveTruck(), act.to != truck_at[i]))
        # SailBoat: to must be different from current location
        s.add(Implies(act.is_SailBoat(), act.to != boat_at[i]))
        
        # LoadTruck_p1: package1 must be at the truck's location and not on any vehicle
        s.add(Implies(act == Action.LoadTruck_p1, 
                      And(p1_veh[i] == VehicleType.none, 
                          p1_loc[i] == truck_at[i])))
        # LoadBoat_p1: package1 must be at the boat's location and not on any vehicle
        s.add(Implies(act == Action.LoadBoat_p1, 
                      And(p1_veh[i] == VehicleType.none, 
                          p1_loc[i] == boat_at[i])))
        # UnloadTruck_p1: package1 must be on the truck
        s.add(Implies(act == Action.UnloadTruck_p1, 
                      p1_veh[i] == VehicleType.truck))
        # UnloadBoat_p1: package1 must be on the boat
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
            if is_as(aval, Action.NoOp):
                plan.append('NoOp')
            elif is_as(aval, Action.DriveTruck):
                to_val = aval.to
                to_name = ['D', 'G', 'M', 'H'][to_val.as_long()]
                plan.append(f'DriveTruck(to={to_name})')
            elif is_as(aval, Action.SailBoat):
                to_val = aval.to
                to_name = ['D', 'G', 'M', 'H'][to_val.as_long()]
                plan.append(f'SailBoat(to={to_name})')
            else:
                # For the load/unload actions, we can use the constructor name
                plan.append(str(aval))
        print("Plan found:")
        for i, act in enumerate(plan):
            print(f"Step {i}: {act}")
    else:
        print("No plan found")

def is_as(v, constructor):
    return v.decl().eq(constructor)

if __name__ == "__main__":
    main()