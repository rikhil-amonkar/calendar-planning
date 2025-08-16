import json
from z3 import *

def main():
    # Define EnumSorts for Names and House Styles
    Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
    HouseStyle, (victorian, colonial) = EnumSort('HouseStyle', ['victorian', 'colonial'])

    # Variables for each house's attributes
    name1 = Const('name1', Name)
    style1 = Const('style1', HouseStyle)
    name2 = Const('name2', Name)
    style2 = Const('style2', HouseStyle)

    # Solver instance
    s = Solver()

    # Constraints based on the clues
    s.add(name1 == Eric)  # Eric is in the first house
    s.add(name1 != name2)  # Unique names per house
    s.add(style1 != style2)  # Unique house styles
    s.add(style1 == victorian)  # Victorian is to the left of Colonial (i.e., in house 1)

    # Check for solution
    if s.check() == sat:
        m = s.model()
        # Extract values from the model
        house1_name = m[name1].sexpr()
        house1_style = m[style1].sexpr()
        house2_name = m[name2].sexpr()
        house2_style = m[style2].sexpr()

        # Construct the JSON solution
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": [
                    ["1", house1_name, house1_style],
                    ["2", house2_name, house2_style]
                ]
            }
        }

        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()