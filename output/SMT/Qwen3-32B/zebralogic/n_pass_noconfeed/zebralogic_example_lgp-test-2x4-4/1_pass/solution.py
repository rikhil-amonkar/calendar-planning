import z3
import json

def main():
    # Define EnumSorts
    Name, (Eric, Arnold) = z3.EnumSort('Name', ['Eric', 'Arnold'])
    HouseStyle, (Victorian, Colonial) = z3.EnumSort('HouseStyle', ['victorian', 'colonial'])
    Height, (VeryShort, Short) = z3.EnumSort('Height', ['very short', 'short'])
    Education, (Associate, HighSchool) = z3.EnumSort('Education', ['associate', 'high school'])

    # Create variables for each house's attributes
    # House 1
    name1 = z3.Const('name1', Name)
    style1 = z3.Const('style1', HouseStyle)
    height1 = z3.Const('height1', Height)
    education1 = z3.Const('education1', Education)
    # House 2
    name2 = z3.Const('name2', Name)
    style2 = z3.Const('style2', HouseStyle)
    height2 = z3.Const('height2', Height)
    education2 = z3.Const('education2', Education)

    solver = z3.Solver()

    # Add uniqueness constraints
    solver.add(name1 != name2)
    solver.add(style1 != style2)
    solver.add(height1 != height2)
    solver.add(education1 != education2)

    # Add puzzle constraints
    # Clue 2: Victorian in first house
    solver.add(style1 == Victorian)
    # Clue 1: short is directly left of Eric => house1 is short, house2 is Eric
    solver.add(height1 == Short)
    solver.add(name2 == Eric)
    # Clue 3: short has associate
    solver.add(education1 == Associate)

    # Check satisfiability
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract values for house 1 and 2
        # House 1
        h1_name = str(model.eval(name1))
        h1_style = str(model.eval(style1))
        h1_height = str(model.eval(height1))
        h1_education = str(model.eval(education1))
        # House 2
        h2_name = str(model.eval(name2))
        h2_style = str(model.eval(style2))
        h2_height = str(model.eval(height2))
        h2_education = str(model.eval(education2))
        # Construct the JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                "rows": [
                    ["1", h1_name, h1_style, h1_height, h1_education],
                    ["2", h2_name, h2_style, h2_height, h2_education]
                ]
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()