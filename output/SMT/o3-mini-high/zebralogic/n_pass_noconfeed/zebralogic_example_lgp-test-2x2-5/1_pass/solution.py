from z3 import *
import json

def main():
    solver = Solver()
    
    # There are 2 houses: House 1 and House 2
    # We'll represent names as: 0 = "Eric", 1 = "Arnold"
    # And house styles as: 0 = "victorian", 1 = "colonial"
    name_vars = [Int("name_1"), Int("name_2")]
    style_vars = [Int("style_1"), Int("style_2")]
    
    # Each variable should be in the domain {0, 1}
    for var in name_vars:
        solver.add(Or(var == 0, var == 1))
    for var in style_vars:
        solver.add(Or(var == 0, var == 1))
    
    # Each house has a unique name and a unique house style.
    solver.add(name_vars[0] != name_vars[1])
    solver.add(style_vars[0] != style_vars[1])
    
    # Clue 2: Eric is in the first house.
    # Represent Eric as 0.
    solver.add(name_vars[0] == 0)
    
    # Clue 1: The person residing in a Victorian house is somewhere to the left of the person living in a Colonial-style house.
    # In a 2-house scenario, this means that House 1 must be victorian (0) and House 2 must be colonial (1).
    solver.add(style_vars[0] == 0)
    solver.add(style_vars[1] == 1)
    
    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        num_to_name = {0: "Eric", 1: "Arnold"}
        num_to_style = {0: "victorian", 1: "colonial"}
        rows = []
        # The houses are in order: House 1 and then House 2.
        for i in range(2):
            house_number = str(i + 1)
            name_val = model.evaluate(name_vars[i]).as_long()
            style_val = model.evaluate(style_vars[i]).as_long()
            rows.append([house_number, num_to_name[name_val], num_to_style[style_val]])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution"}))

if __name__ == "__main__":
    main()