from z3 import *

def main():
    for n_steps in range(4, 11):  # Try step counts from 4 to 10
        states = list(range(n_steps + 1))
        
        monkey_loc = [Int(f'monkey_loc_{i}') for i in states]
        box_loc = [Int(f'box_loc_{i}') for i in states]
        monkey_on_box = [Bool(f'monkey_on_box_{i}') for i in states]
        monkey_has_banana = [Bool(f'monkey_has_banana_{i}') for i in states]
        actions = [Int(f'action_{i}') for i in range(n_steps)]
        
        solver = Solver()
        
        # Initial state
        solver.add(monkey_loc[0] == 0)  # A
        solver.add(box_loc[0] == 1)     # B
        solver.add(Not(monkey_on_box[0]))
        solver.add(Not(monkey_has_banana[0]))
        
        # Goal state
        solver.add(monkey_has_banana[n_steps])
        
        # Domain constraints for locations
        for i in states:
            solver.add(Or(monkey_loc[i] == 0, monkey_loc[i] == 1, monkey_loc[i] == 2))
            solver.add(Or(box_loc[i] == 0, box_loc[i] == 1, box_loc[i] == 2))
        
        # Action constraints for each step
        for i in range(n_steps):
            # Constraint: Once box is at C, keep it there
            solver.add(Implies(box_loc[i] == 2, box_loc[i+1] == 2))
            
            # Constraint: Monkey stays at C when box is there
            solver.add(Implies(And(box_loc[i] == 2, monkey_loc[i] == 2), 
                             monkey_loc[i+1] == 2))
            
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
            
            # Move from B to A
            cases.append(And(
                actions[i] == 1,
                monkey_loc[i] == 1,
                Not(monkey_on_box[i]),
                monkey_loc[i+1] == 0,
                box_loc[i+1] == box_loc[i],
                monkey_on_box[i+1] == monkey_on_box[i],
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            # Move from B to C
            cases.append(And(
                actions[i] == 2,
                monkey_loc[i] == 1,
                Not(monkey_on_box[i]),
                monkey_loc[i+1] == 2,
                box_loc[i+1] == box_loc[i],
                monkey_on_box[i+1] == monkey_on_box[i],
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            # Move from C to B
            cases.append(And(
                actions[i] == 3,
                monkey_loc[i] == 2,
                Not(monkey_on_box[i]),
                monkey_loc[i+1] == 1,
                box_loc[i+1] == box_loc[i],
                monkey_on_box[i+1] == monkey_on_box[i],
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            # Climb at A
            cases.append(And(
                actions[i] == 4,
                monkey_loc[i] == 0,
                box_loc[i] == 0,
                Not(monkey_on_box[i]),
                monkey_on_box[i+1],
                monkey_loc[i+1] == 0,
                box_loc[i+1] == 0,
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            # Climb at B
            cases.append(And(
                actions[i] == 5,
                monkey_loc[i] == 1,
                box_loc[i] == 1,
                Not(monkey_on_box[i]),
                monkey_on_box[i+1],
                monkey_loc[i+1] == 1,
                box_loc[i+1] == 1,
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            # Climb at C
            cases.append(And(
                actions[i] == 6,
                monkey_loc[i] == 2,
                box_loc[i] == 2,
                Not(monkey_on_box[i]),
                monkey_on_box[i+1],
                monkey_loc[i+1] == 2,
                box_loc[i+1] == 2,
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            # Push from A to B
            cases.append(And(
                actions[i] == 7,
                monkey_loc[i] == 0,
                box_loc[i] == 0,
                Not(monkey_on_box[i]),
                monkey_loc[i+1] == 1,
                box_loc[i+1] == 1,
                Not(monkey_on_box[i+1]),
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            # Push from B to A
            cases.append(And(
                actions[i] == 8,
                monkey_loc[i] == 1,
                box_loc[i] == 1,
                Not(monkey_on_box[i]),
                monkey_loc[i+1] == 0,
                box_loc[i+1] == 0,
                Not(monkey_on_box[i+1]),
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            # Push from B to C
            cases.append(And(
                actions[i] == 9,
                monkey_loc[i] == 1,
                box_loc[i] == 1,
                Not(monkey_on_box[i]),
                monkey_loc[i+1] == 2,
                box_loc[i+1] == 2,
                Not(monkey_on_box[i+1]),
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            # Push from C to B
            cases.append(And(
                actions[i] == 10,
                monkey_loc[i] == 2,
                box_loc[i] == 2,
                Not(monkey_on_box[i]),
                monkey_loc[i+1] == 1,
                box_loc[i+1] == 1,
                Not(monkey_on_box[i+1]),
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            # Grasp banana
            cases.append(And(
                actions[i] == 11,
                monkey_on_box[i],
                monkey_loc[i] == 2,
                Not(monkey_has_banana[i]),
                monkey_has_banana[i+1],
                monkey_loc[i+1] == monkey_loc[i],
                box_loc[i+1] == box_loc[i],
                monkey_on_box[i+1] == monkey_on_box[i]
            ))
            
            # No-op action
            cases.append(And(
                actions[i] == 12,
                monkey_loc[i+1] == monkey_loc[i],
                box_loc[i+1] == box_loc[i],
                monkey_on_box[i+1] == monkey_on_box[i],
                monkey_has_banana[i+1] == monkey_has_banana[i]
            ))
            
            solver.add(Or(cases))
        
        if solver.check() == sat:
            model = solver.model()
            action_names = {
                0: "move_A_B",
                1: "move_B_A",
                2: "move_B_C",
                3: "move_C_B",
                4: "climb_A",
                5: "climb_B",
                6: "climb_C",
                7: "push_A_B",
                8: "push_B_A",
                9: "push_B_C",
                10: "push_C_B",
                11: "grasp",
                12: "noop"
            }
            plan = []
            for i in range(n_steps):
                action_val = model[actions[i]].as_long()
                plan.append(action_names[action_val])
            print(f"Plan found in {n_steps} steps:")
            for step, action in enumerate(plan):
                print(f"Step {step}: {action}")
            return
    print("No plan found within 10 steps")

if __name__ == "__main__":
    main()