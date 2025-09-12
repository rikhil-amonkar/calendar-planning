import json
from z3 import *

def main():
    # Define EnumSorts for names and house styles
    Names, (Eric, Arnold) = EnumSort('Names', ['Eric', 'Arnold'])
    HouseStyles, (Victorian, Colonial) = EnumSort('HouseStyles', ['victorian', 'colonial'])

    # Variables for each house's attributes
    name1 = Const('name1', Names)
    name2 = Const('name2', Names)
    style1 = Const('style1', HouseStyles)
    style2 = Const('style2', HouseStyles)

    # Create solver instance and add constraints
    s = Solver()
    
    # Clue 2: Eric is in the first house
    s.add(name1 == Eric)
    
    # Each name and style must be unique
    s.add(name1 != name2)
    s.add(style1 != style2)
    
    # Clue 1: Victorian is to the left of Colonial => style1 is Victorian
    s.add(style1 == Victorian)

    # Check for solution
    if s.check() == sat:
        model = s.model()
        
        # Extract values from the model
        name1_val = model.evaluate(name1).decl().name()
        name2_val = model.evaluate(name2).decl().name()
        style1_val = model.evaluate(style1).decl().name()
        style2_val = model.evaluate(style2).decl().name()

        # Construct the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": [
                    ["1", name1_val, style1_val],
                    ["2", name2_val, style2_val]
                ]
            }
        }

        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()