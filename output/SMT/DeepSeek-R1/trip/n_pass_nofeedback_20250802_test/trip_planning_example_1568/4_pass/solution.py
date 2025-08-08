from z3 import *

def solve_monkey_banana():
    # Locations: A=0, B=1, C=2
    n_locations = 3
    # Actions: 0=Move, 1=Push, 2=ClimbUp, 3=ClimbDown, 4=Grasp, 5=Release
    n_actions = 6
    # Action parameters: (action_type, from_loc, to_loc) for Move/Push, (action_type, loc) for others
    action_list = [
        (0, 0, 1),   # Move A->B
        (0, 1, 0),   # Move B->A
        (0, 1, 2),   # Move B->C
        (0, 2, 1),   # Move C->B
        (1, 0, 1),   # Push A->B
        (1, 1, 0),   # Push B->A
        (1, 1, 2),   # Push B->C
        (1, 2, 1),   # Push C->B
        (2, 0),      # ClimbUp at A
        (2, 1),      # ClimbUp at B
        (2, 2),      # ClimbUp at C
        (3, 0),      # ClimbDown at A
        (3, 1),      # ClimbDown at B
        (3, 2),      # ClimbDown at C
        (4, 2),      # Grasp at C
        (5, 2)       # Release at C
    ]
    n_action_instances = len(action_list)
    
    # Try increasing time horizons
    for T in range(4, 11):
        # Create state variables for T+1 steps
        M = [Int(f'M_{i}') for i in range(T+1)]  # Monkey location
        B = [Int(f'B_{i}') for i in range(T+1)]  # Box location
        F = [Bool(f'F_{i}') for i in range(T+1)] # Monkey on floor
        H = [Bool(f'H_{i}') for i in range(T+1)] # Has bananas
        
        # Action variables for T steps
        a = [Int(f'a_{i}') for i in range(T)]
        
        s = Solver()
        
        # Initial state: monkey at A, box at B, on floor, no bananas
        s.add(M[0] == 0, B[0] == 1, F[0] == True, H[0] == False)
        
        # Goal: monkey has bananas
        s.add(H[T] == True)
        
        # State variables domain constraints
        for i in range(T+1):
            s.add(And(M[i] >= 0, M[i] < n_locations))
            s.add(And(B[i] >= 0, B[i] < n_locations))
        
        # Action variables domain constraints
        for i in range(T):
            s.add(And(a[i] >= 0, a[i] < n_action_instances))
        
        # Constraints for each time step
        for t in range(T):
            constraints = []
            for idx, act in enumerate(action_list):
                if act[0] == 0:  # Move
                    from_loc, to_loc = act[1], act[2]
                    # Precondition: monkey at from_loc and on floor
                    prec = And(M[t] == from_loc, F[t] == True)
                    # Effect: monkey moves to to_loc, other state unchanged
                    eff = And(M[t+1] == to_loc, B[t+1] == B[t], F[t+1] == F[t], H[t+1] == H[t])
                elif act[0] == 1:  # Push
                    from_loc, to_loc = act[1], act[2]
                    # Precondition: monkey and box at from_loc, monkey on floor
                    prec = And(M[t] == from_loc, B[t] == from_loc, F[t] == True)
                    # Effect: both move to to_loc, monkey remains on floor
                    eff = And(M[t+1] == to_loc, B[t+1] == to_loc, F[t+1] == True, H[t+1] == H[t])
                elif act[0] == 2:  # ClimbUp
                    loc = act[1]
                    # Precondition: monkey and box at loc, monkey on floor
                    prec = And(M[t] == loc, B[t] == loc, F[t] == True)
                    # Effect: monkey climbs box (no longer on floor)
                    eff = And(M[t+1] == loc, B[t+1] == loc, F[t+1] == False, H[t+1] == H[t])
                elif act[0] == 3:  # ClimbDown
                    loc = act[1]
                    # Precondition: monkey and box at loc, monkey not on floor
                    prec = And(M[t] == loc, B[t] == loc, F[t] == False)
                    # Effect: monkey descends to floor
                    eff = And(M[t+1] == loc, B[t+1] == loc, F[t+1] == True, H[t+1] == H[t])
                elif act[0] == 4:  # Grasp
                    loc = act[1]
                    # Precondition: monkey at loc, on box, doesn't have bananas
                    prec = And(M[t] == loc, F[t] == False, H[t] == False)
                    # Effect: monkey grasps bananas
                    eff = And(M[t+1] == M[t], B[t+1] == B[t], F[t+1] == F[t], H[t+1] == True)
                elif act[0] == 5:  # Release
                    loc = act[1]
                    # Precondition: monkey at loc, on box, has bananas
                    prec = And(M[t] == loc, F[t] == False, H[t] == True)
                    # Effect: monkey releases bananas
                    eff = And(M[t+1] == M[t], B[t+1] == B[t], F[t+1] == F[t], H[t+1] == False)
                else:
                    prec = BoolVal(False)
                    eff = BoolVal(False)
                
                constraints.append(Implies(a[t] == idx, And(prec, eff)))
            
            s.add(Or(constraints))
        
        if s.check() == sat:
            m = s.model()
            plan = []
            loc_names = {0: 'A', 1: 'B', 2: 'C'}
            for t in range(T):
                idx = m.evaluate(a[t]).as_long()
                act = action_list[idx]
                if act[0] == 0:  # Move
                    plan.append(f"Move({loc_names[act[1]]}, {loc_names[act[2]]})")
                elif act[0] == 1:  # Push
                    plan.append(f"Push({loc_names[act[1]]}, {loc_names[act[2]]})")
                elif act[0] == 2:  # ClimbUp
                    plan.append(f"ClimbUp({loc_names[act[1]]})")
                elif act[0] == 3:  # ClimbDown
                    plan.append(f"ClimbDown({loc_names[act[1]]})")
                elif act[0] == 4:  # Grasp
                    plan.append(f"Grasp({loc_names[act[1]]})")
                elif act[0] == 5:  # Release
                    plan.append(f"Release({loc_names[act[1]]})")
            print(f"Plan found with {T} steps:")
            for i, action in enumerate(plan):
                print(f"Step {i}: {action}")
            return
        
    print("No solution found for T <= 10")

solve_monkey_banana()