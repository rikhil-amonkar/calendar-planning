import json
from z3 import *

def solve_z3():
    # Define EnumSorts
    Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
    Height, (very_short, short) = EnumSort('Height', ['very_short', 'short'])
    Education, (associate, high_school) = EnumSort('Education', ['associate', 'high_school'])

    # Create variables for each house's attributes
    name1 = Const('name1', Name)
    name2 = Const('name2', Name)

    height1 = Const('height1', Height)
    height2 = Const('height2', Height)

    education1 = Const('education1', Education)
    education2 = Const('education2', Education)

    s = Solver()

    # Add constraints for uniqueness between houses
    s.add(name1 != name2)
    s.add(height1 != height2)
    s.add(education1 != education2)

    # Add clues as constraints
    s.add(height1 == short)  # Clue 1: short is in house 1
    s.add(name2 == Eric)     # Clue 1: Eric is in house 2
    s.add(education1 == associate)  # Clue 3: short (house1) has associate

    # Check if the constraints are satisfied
    if s.check() == sat:
        model = s.model()
        # Extract values
        n1 = model[name1]
        h1 = model[height1]
        e1 = model[education1]

        n2 = model[name2]
        h2 = model[height2]
        e2 = model[education2]

        # Convert to strings with proper formatting
        h1_str = str(h1).replace('_', ' ')
        e1_str = str(e1).replace('_', ' ')
        h2_str = str(h2).replace('_', ' ')
        e2_str = str(e2).replace('_', ' ')

        # Now build the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                "rows": [
                    ["1", str(n1), "victorian", h1_str, e1_str],
                    ["2", str(n2), "colonial", h2_str, e2_str]
                ]
            }
        }
        return solution
    else:
        return None  # No solution found

if __name__ == "__main__":
    solution = solve_z3()
    print(json.dumps(solution, indent=2))