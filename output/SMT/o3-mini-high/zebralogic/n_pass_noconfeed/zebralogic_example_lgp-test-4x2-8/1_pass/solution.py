from z3 import *
import json

def main():
    # Create solver instance
    solver = Solver()

    # Define integer variables for persons (their house positions)
    Peter = Int("Peter")
    Arnold = Int("Arnold")
    Alice = Int("Alice")
    Eric = Int("Eric")
    
    # Define integer variables for colors (the house positions for each favorite color)
    Yellow = Int("Yellow")
    Green = Int("Green")
    Red = Int("Red")
    White = Int("White")
    
    houses = [1, 2, 3, 4]

    # Domain constraints: each variable must be in {1,2,3,4}
    for var in [Peter, Arnold, Alice, Eric, Yellow, Green, Red, White]:
        solver.add(var >= 1, var <= 4)
    
    # All persons must be in distinct houses
    solver.add(Distinct(Peter, Arnold, Alice, Eric))
    # All colors must be assigned to distinct houses
    solver.add(Distinct(Yellow, Green, Red, White))
    
    # Apply the puzzle constraints:

    # Clue 1: The person whose favorite color is green is in the third house.
    solver.add(Green == 3)
    
    # Clue 2: Peter is in the first house.
    solver.add(Peter == 1)
    
    # Clue 3: There is one house between the person whose favorite color is red and the person who loves yellow.
    solver.add(Abs(Red - Yellow) == 2)
    
    # Clue 4: Arnold is directly left of Eric.
    solver.add(Arnold + 1 == Eric)
    
    # Clue 5: Eric is the person who loves yellow.
    solver.add(Eric == Yellow)
    
    # Check if the constraints are solvable
    if solver.check() == sat:
        model = solver.model()
        
        # Gather the assignments into dictionaries
        person_positions = {
            "Peter": model[Peter].as_long(),
            "Arnold": model[Arnold].as_long(),
            "Alice": model[Alice].as_long(),
            "Eric": model[Eric].as_long()
        }
        color_positions = {
            "yellow": model[Yellow].as_long(),
            "green": model[Green].as_long(),
            "red": model[Red].as_long(),
            "white": model[White].as_long()
        }
        
        # Prepare rows sorted by house number (1 to 4)
        rows = []
        for house in sorted(houses):
            # Determine which person is in the current house.
            person_in_house = None
            for name, pos in person_positions.items():
                if pos == house:
                    person_in_house = name
                    break
            
            # Determine which color is assigned to the current house.
            color_in_house = None
            for color, pos in color_positions.items():
                if pos == house:
                    color_in_house = color
                    break
            
            # Create the row as specified. House number as string.
            rows.append([str(house), person_in_house, color_in_house])
        
        # Build the output JSON in the required format
        output = {
            "solution": {
                "header": ["House", "Name", "Color"],
                "rows": rows
            }
        }
        # Print out the JSON formatted result.
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()