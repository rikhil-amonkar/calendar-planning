from z3 import *

def solve_monkey_banana(T):
    # Locations: A=0, B=1, C=2
    n_locations = 3
    n_actions = 16  # Total actions defined (4 Move + 4 Push + 3 ClimbUp + 3 ClimbDown + 1 Grasp + 1 Release)

    # Action list: (type, params...)
    action_list = [
        (0, 0, 1),   # Move A->B
        (0, 1, 0),   # Move B->A
        (0, 1, 2),   # Move B->C
        (0, 2, 1),   # Move C->B
        (1, 0, 1),   # Push A->B (monkey to B)
        (1, 1, 0),   # Push B->A (monkey to A)
        (1, 1, 2),   # Push B->C (monkey to C)
        (1, 2, 1),   # Push C->B (monkey to B)
        (2, 0),      # ClimbUp at A
        (2, 1),      # ClimbUp at B
        (2, 2),      # ClimbUp at C
        (3, 0),      # ClimbDown at A
        (3, 1),      # ClimbDown at B
        (3, 2),      # ClimbDown at C
        (4, 2),      # Grasp at C
        (5, 2)       # Release at C
    ]

    # Create state variables for T+1 steps
    M = [Int(f'M_{i}') for i in range(T+1)]  # Monkey location
    B = [Int(f'B_{i}') for i in range(T+1)]  # Box location
    F = [Bool(f'F_{i}') for i in range(T+1)] # Monkey on floor
    H = [Bool(f'H_{i}') for i in range(T+1)] # Has bananas

    # Action variables for T steps
    a = [Int(f'a_{i}') for i in range(T)]

    s = Solver()

    # Initial state constraints
    s.add(M[0] == 0, B[0] == 1, F[0] == True, H[0] == False)

    # Final goal
    s.add(H[T] == True)

    # State variables domain constraints
    for i in range(T+1):
        s.add(And(M[i] >= 0, M[i] < n_locations))
        s.add(And(B[i] >= 0, B[i] < n_locations))

    # Action variables domain constraints
    for i in range(T):
        s.add(And(a[i] >= 0, a[i] < n_actions))

    # Constraints for each time step t
    for t in range(T):
        # Preconditions and effects for each possible action
        constraints = []
        for idx, act in enumerate(action_list):
            if act[0] == 0:  # Move
                from_loc = act[1]
                to_loc = act[2]
                prec = And(M[t] == from_loc, F[t] == True)
                eff = And(M[t+1] == to_loc, B[t+1] == B[t], F[t+1] == True, H[t+1] == H[t])
            elif act[0] == 1:  # Push
                from_loc = act[1]
                to_loc = act[2]
                prec = And(M[t] == from_loc, B[t] == from_loc, F[t] == True)
                eff = And(M[t+1] == to_loc, B[t+1] == to_loc, F[t+1] == True, H[t+1] == H[t])
            elif act[0] == 2:  # ClimbUp
                x = act[1]
                prec = And(M[t] == x, B[t] == x, F[t] == True)
                eff = And(M[t+1] == x, B[t+1] == x, F[t+1] == False, H[t+1] == H[t])
            elif act[0] == 3:  # ClimbDown
                x = act[1]
                prec = And(M[t] == x, B[t] == x, F[t] == False)
                eff = And(M[t+1] == x, B[t+1] == x, F[t+1] == True, H[t+1] == H[t])
            elif act[0] == 4:  # Grasp
                x = act[1]
                prec = And(M[t] == x, F[t] == False, H[t] == False)
                eff = And(M[t+1] == M[t], B[t+1] == B[t], F[t+1] == F[t], H[t+1] == True)
            elif act[0] == 5:  # Release
                x = act[1]
                prec = And(M[t] == x, F[t] == False, H[t] == True)
                eff = And(M[t+1] == M[t], B[t+1] == B[t], F[t+1] == F[t], H[t+1] == False)
            else:
                prec = BoolVal(False)
                eff = BoolVal(False)
            constraints.append(Implies(a[t] == idx, And(prec, eff)))
        s.add(And(constraints))

    if s.check() == sat:
        m = s.model()
        plan = []
        loc_names = ['A', 'B', 'C']
        for t in range(T):
            idx = m.evaluate(a[t]).as_long()
            act_desc = action_list[idx]
            if act_desc[0] == 0:
                plan.append(f"Move({loc_names[act_desc[1]]}, {loc_names[act_desc[2]]})")
            elif act_desc[0] == 1:
                plan.append(f"Push({loc_names[act_desc[1]]}, {loc_names[act_desc[2]]})")
            elif act_desc[0] == 2:
                plan.append(f"ClimbUp({loc_names[act_desc[1]]})")
            elif act_desc[0] == 3:
                plan.append(f"ClimbDown({loc_names[act_desc[1]]})")
            elif act_desc[0] == 4:
                plan.append(f"Grasp({loc_names[act_desc[1]]})")
            elif act_desc[0] == 5:
                plan.append(f"Release({loc_names[act_desc[1]]})")
        return plan
    else:
        return None

# Find minimal T with a solution
T = 4
plan = None
while T <= 10:
    plan = solve_monkey_banana(T)
    if plan is not None:
        print("Plan found with T =", T)
        for i, action in enumerate(plan):
            print(f"Step {i}: {action}")
        break
    T += 1
if plan is None:
    print("No solution found for T up to 10")