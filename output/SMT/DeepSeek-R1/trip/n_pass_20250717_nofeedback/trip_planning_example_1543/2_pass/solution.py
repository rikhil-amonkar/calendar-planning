from z3 import *

def monkey_banana_plan():
    # Create solver
    s = Solver()

    # Locations: A=0, B=1, C=2
    locs = [0, 1, 2]
    A, B, C = 0, 1, 2

    # State variables for time steps 0 to 4 (5 steps)
    monkey_loc = [Int(f'monkey_loc_{i}') for i in range(5)]
    box_loc = [Int(f'box_loc_{i}') for i in range(5)]
    on_box = [Bool(f'on_box_{i}') for i in range(5)]
    has_banana = [Bool(f'has_banana_{i}') for i in range(5)]

    # Action variables for time steps 0 to 3 (4 actions)
    # Action kind: 0=walk, 1=push_box, 2=climb_on, 3=grasp
    act_kind = [Int(f'act_kind_{i}') for i in range(4)]
    # Location parameter for actions (used for walk and push_box, arbitrary for others)
    act_loc = [Int(f'act_loc_{i}') for i in range(4)]

    # Initial state constraints (t=0)
    s.add(monkey_loc[0] == A)
    s.add(box_loc[0] == C)
    s.add(on_box[0] == False)
    s.add(has_banana[0] == False)

    # Goal state (t=4)
    s.add(has_banana[4] == True)

    # Constraints for each action step t=0 to 3
    for t in range(4):
        # Ensure action kind is valid (0 to 3)
        s.add(act_kind[t] >= 0, act_kind[t] <= 3)
        # Ensure action location is valid (0,1,2)
        s.add(Or([act_loc[t] == loc for loc in locs]))

        # Preconditions based on action kind
        if t < 4:  # Ensure we don't go out of bounds
            if t == 0:
                current_monkey = monkey_loc[0]
                current_box = box_loc[0]
                current_on_box = on_box[0]
            else:
                current_monkey = monkey_loc[t]
                current_box = box_loc[t]
                current_on_box = on_box[t]

            # Precondition for walk
            s.add(Implies(act_kind[t] == 0, 
                          And(current_monkey != act_loc[t], 
                              Not(current_on_box))))
            # Precondition for push_box
            s.add(Implies(act_kind[t] == 1, 
                          And(current_monkey == current_box, 
                              current_monkey != act_loc[t], 
                              Not(current_on_box))))
            # Precondition for climb_on
            s.add(Implies(act_kind[t] == 2, 
                          And(current_monkey == current_box, 
                              Not(current_on_box))))
            # Precondition for grasp
            s.add(Implies(act_kind[t] == 3, 
                          And(current_on_box, current_box == B)))

        # State transitions for the next time step (t+1)
        # Monkey location transition
        s.add(monkey_loc[t+1] == If(act_kind[t] == 0, act_loc[t],
                                 If(act_kind[t] == 1, act_loc[t],
                                 monkey_loc[t])))
        # Box location transition
        s.add(box_loc[t+1] == If(act_kind[t] == 1, act_loc[t], box_loc[t]))
        # On_box transition
        s.add(on_box[t+1] == If(act_kind[t] == 2, True, on_box[t]))
        # Has_banana transition
        s.add(has_banana[t+1] == If(act_kind[t] == 3, True, has_banana[t]))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Helper function to convert location index to letter
        def loc_to_letter(loc_val):
            if loc_val == 0:
                return 'A'
            elif loc_val == 1:
                return 'B'
            elif loc_val == 2:
                return 'C'
            return str(loc_val)

        # Print the plan
        plan = []
        for t in range(4):
            kind = m[act_kind[t]].as_long()
            loc_val = m[act_loc[t]].as_long()
            if kind == 0:
                plan.append(f"walk({loc_to_letter(loc_val)})")
            elif kind == 1:
                plan.append(f"push_box({loc_to_letter(loc_val)})")
            elif kind == 2:
                plan.append("climb_on")
            elif kind == 3:
                plan.append("grasp")
            else:
                plan.append(f"unknown action (kind={kind})")
        print("Plan found:")
        for i, action in enumerate(plan):
            print(f"Step {i+1}: {action}")
        return plan
    else:
        print("No plan found")
        return None

# Call the function to find and print the plan
monkey_banana_plan()