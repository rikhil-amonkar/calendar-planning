from z3 import *

def monkey_banana_plan():
    s = Solver()
    # Locations: A=0, B=1, C=2
    A, B, C = 0, 1, 2
    locs = [A, B, C]
    location_names = {A: 'A', B: 'B', C: 'C'}
    
    # State variables for 5 time steps (0 to 4)
    monkey_loc = [Int(f'monkey_loc_{i}') for i in range(5)]
    box_loc = [Int(f'box_loc_{i}') for i in range(5)]
    on_box = [Bool(f'on_box_{i}') for i in range(5)]
    has_banana = [Bool(f'has_banana_{i}') for i in range(5)]
    
    # Action variables for 4 steps (0 to 3)
    # Action kinds: 0=walk, 1=push_box, 2=climb_on, 3=grasp
    act_kind = [Int(f'act_kind_{i}') for i in range(4)]
    act_loc = [Int(f'act_loc_{i}') for i in range(4)]  # Target location for walk/push_box
    
    # Initial state (t=0)
    s.add(monkey_loc[0] == A)
    s.add(box_loc[0] == C)
    s.add(on_box[0] == False)
    s.add(has_banana[0] == False)
    
    # Goal state (t=4)
    s.add(has_banana[4] == True)
    
    # Constraint: If monkey is on box, it must be at same location as box
    for t in range(5):
        s.add(Implies(on_box[t], monkey_loc[t] == box_loc[t]))
    
    # Constraints for each action step
    for t in range(4):
        # Valid action kind and location
        s.add(act_kind[t] >= 0, act_kind[t] <= 3)
        s.add(Or([act_loc[t] == loc for loc in locs]))
        
        # Current state (for preconditions)
        current_monkey = monkey_loc[t]
        current_box = box_loc[t]
        current_on_box = on_box[t]
        current_has_banana = has_banana[t]
        
        # Preconditions
        walk_pre = And(current_monkey != act_loc[t], Not(current_on_box))
        push_pre = And(current_monkey == current_box, 
                       current_monkey != act_loc[t], 
                       Not(current_on_box))
        climb_pre = And(current_monkey == current_box, Not(current_on_box))
        grasp_pre = And(current_on_box, current_box == B, Not(current_has_banana))
        
        s.add(Implies(act_kind[t] == 0, walk_pre))
        s.add(Implies(act_kind[t] == 1, push_pre))
        s.add(Implies(act_kind[t] == 2, climb_pre))
        s.add(Implies(act_kind[t] == 3, grasp_pre))
        
        # State transitions
        # Monkey location: moves to target if walking or pushing box, otherwise stays
        s.add(monkey_loc[t+1] == If(
            Or(act_kind[t] == 0, act_kind[t] == 1),
            act_loc[t],
            current_monkey
        ))
        
        # Box location: moves only if pushing box
        s.add(box_loc[t+1] == If(
            act_kind[t] == 1,
            act_loc[t],
            current_box
        ))
        
        # On box: true only if climbing on
        s.add(on_box[t+1] == If(
            act_kind[t] == 2,
            True,
            # If pushing box, monkey gets off (if previously on)
            If(act_kind[t] == 1, False, current_on_box)
        ))
        
        # Has banana: true only if grasping
        s.add(has_banana[t+1] == If(
            act_kind[t] == 3,
            True,
            current_has_banana
        ))
    
    # Solve and output plan
    if s.check() == sat:
        m = s.model()
        plan = []
        for t in range(4):
            kind_val = m.evaluate(act_kind[t]).as_long()
            loc_val = m.evaluate(act_loc[t]).as_long()
            if kind_val == 0:
                plan.append(f"walk({location_names[loc_val]})")
            elif kind_val == 1:
                plan.append(f"push_box({location_names[loc_val]})")
            elif kind_val == 2:
                plan.append("climb_on")
            elif kind_val == 3:
                plan.append("grasp")
        print("Valid plan found:")
        for i, action in enumerate(plan):
            print(f"Step {i+1}: {action}")
        return plan
    else:
        print("No valid plan found")
        return None

# Execute the planning function
monkey_banana_plan()