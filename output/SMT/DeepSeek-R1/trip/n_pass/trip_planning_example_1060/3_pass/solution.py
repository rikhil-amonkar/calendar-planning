from z3 import *

def main():
    n_steps = 10
    states = list(range(n_steps + 1))
    
    monkey_loc = [Int('monkey_loc_%d' % i) for i in states]
    box_loc = [Int('box_loc_%d' % i) for i in states]
    monkey_on_box = [Bool('monkey_on_box_%d' % i) for i in states]
    monkey_has_banana = [Bool('monkey_has_banana_%d' % i) for i in states]
    actions = [Int('action_%d' % i) for i in range(n_steps)]
    
    solver = Solver()
    
    # Initial state
    solver.add(monkey_loc[0] == 0)  # A
    solver.add(box_loc[0] == 1)      # B
    solver.add(monkey_on_box[0] == False)
    solver.add(monkey_has_banana[0] == False)
    
    # Goal state
    solver.add(monkey_has_banana[n_steps] == True)
    
    # Domain constraints for locations
    for i in states:
        solver.add(Or(monkey_loc[i] == 0, monkey_loc[i] == 1, monkey_loc[i] == 2))
        solver.add(Or(box_loc[i] == 0, box_loc[i] == 1, box_loc[i] == 2))
    
    # Action constraints for each step
    for i in range(n_steps):
        cases = []
        
        # Move from A to B
        cases.append(And(
            actions[i] == 0,
            monkey_loc[i] == 0,
            Not(monkey_on_box[i]),
            monkey_loc[i+1] == 1,
            box_loc[i+1] == box_loc[i],
            monkey_on_box[i+1] == monkey_on_box[i],
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Move from A to C
        cases.append(And(
            actions[i] == 1,
            monkey_loc[i] == 0,
            Not(monkey_on_box[i]),
            monkey_loc[i+1] == 2,
            box_loc[i+1] == box_loc[i],
            monkey_on_box[i+1] == monkey_on_box[i],
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Move from B to A
        cases.append(And(
            actions[i] == 2,
            monkey_loc[i] == 1,
            Not(monkey_on_box[i]),
            monkey_loc[i+1] == 0,
            box_loc[i+1] == box_loc[i],
            monkey_on_box[i+1] == monkey_on_box[i],
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Move from B to C
        cases.append(And(
            actions[i] == 3,
            monkey_loc[i] == 1,
            Not(monkey_on_box[i]),
            monkey_loc[i+1] == 2,
            box_loc[i+1] == box_loc[i],
            monkey_on_box[i+1] == monkey_on_box[i],
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Move from C to A
        cases.append(And(
            actions[i] == 4,
            monkey_loc[i] == 2,
            Not(monkey_on_box[i]),
            monkey_loc[i+1] == 0,
            box_loc[i+1] == box_loc[i],
            monkey_on_box[i+1] == monkey_on_box[i],
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Move from C to B
        cases.append(And(
            actions[i] == 5,
            monkey_loc[i] == 2,
            Not(monkey_on_box[i]),
            monkey_loc[i+1] == 1,
            box_loc[i+1] == box_loc[i],
            monkey_on_box[i+1] == monkey_on_box[i],
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Climb at A
        cases.append(And(
            actions[i] == 6,
            monkey_loc[i] == 0,
            box_loc[i] == 0,
            Not(monkey_on_box[i]),
            monkey_on_box[i+1] == True,
            monkey_loc[i+1] == 0,
            box_loc[i+1] == 0,
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Climb at B
        cases.append(And(
            actions[i] == 7,
            monkey_loc[i] == 1,
            box_loc[i] == 1,
            Not(monkey_on_box[i]),
            monkey_on_box[i+1] == True,
            monkey_loc[i+1] == 1,
            box_loc[i+1] == 1,
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Climb at C
        cases.append(And(
            actions[i] == 8,
            monkey_loc[i] == 2,
            box_loc[i] == 2,
            Not(monkey_on_box[i]),
            monkey_on_box[i+1] == True,
            monkey_loc[i+1] == 2,
            box_loc[i+1] == 2,
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Push from A to B (adjacent)
        cases.append(And(
            actions[i] == 9,
            monkey_loc[i] == 0,
            box_loc[i] == 0,
            Not(monkey_on_box[i]),
            monkey_loc[i+1] == 1,
            box_loc[i+1] == 1,
            monkey_on_box[i+1] == monkey_on_box[i],
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Push from B to A (adjacent)
        cases.append(And(
            actions[i] == 10,
            monkey_loc[i] == 1,
            box_loc[i] == 1,
            Not(monkey_on_box[i]),
            monkey_loc[i+1] == 0,
            box_loc[i+1] == 0,
            monkey_on_box[i+1] == monkey_on_box[i],
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Push from B to C (adjacent)
        cases.append(And(
            actions[i] == 11,
            monkey_loc[i] == 1,
            box_loc[i] == 1,
            Not(monkey_on_box[i]),
            monkey_loc[i+1] == 2,
            box_loc[i+1] == 2,
            monkey_on_box[i+1] == monkey_on_box[i],
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Push from C to B (adjacent)
        cases.append(And(
            actions[i] == 12,
            monkey_loc[i] == 2,
            box_loc[i] == 2,
            Not(monkey_on_box[i]),
            monkey_loc[i+1] == 1,
            box_loc[i+1] == 1,
            monkey_on_box[i+1] == monkey_on_box[i],
            monkey_has_banana[i+1] == monkey_has_banana[i]
        ))
        
        # Grasp banana (only at C)
        cases.append(And(
            actions[i] == 13,
            monkey_on_box[i] == True,
            monkey_loc[i] == 2,   # Must be at C
            monkey_has_banana[i] == False,
            monkey_has_banana[i+1] == True,
            monkey_loc[i+1] == monkey_loc[i],
            box_loc[i+1] == box_loc[i],
            monkey_on_box[i+1] == monkey_on_box[i]
        ))
        
        solver.add(Or(cases))
    
    if solver.check() == sat:
        model = solver.model()
        action_names = {
            0: "move_A_B",
            1: "move_A_C",
            2: "move_B_A",
            3: "move_B_C",
            4: "move_C_A",
            5: "move_C_B",
            6: "climb_A",
            7: "climb_B",
            8: "climb_C",
            9: "push_A_B",
            10: "push_B_A",
            11: "push_B_C",
            12: "push_C_B",
            13: "grasp"
        }
        plan = []
        for i in range(n_steps):
            action_val = model[actions[i]].as_long()
            plan.append(action_names[action_val])
        print("Plan found:")
        for step, action in enumerate(plan):
            print(f"Step {step}: {action}")
    else:
        print("No plan found within the step limit.")

if __name__ == "__main__":
    main()