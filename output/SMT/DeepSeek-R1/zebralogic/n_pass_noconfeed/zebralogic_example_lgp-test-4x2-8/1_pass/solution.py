import json
from z3 import *

def main():
    # Create the solver
    solver = Solver()
    
    # Define the enums for names and colors
    NameSort, name_consts = EnumSort('Name', ['Peter', 'Arnold', 'Alice', 'Eric'])
    ColorSort, color_consts = EnumSort('Color', ['yellow', 'green', 'red', 'white'])
    
    # Create constants for each name and color for easier access
    Peter, Arnold, Alice, Eric = name_consts
    yellow, green, red, white = color_consts
    
    # Create variables for each house: name and color
    names = [Const(f'name_{i}', NameSort) for i in range(1, 5)]
    colors = [Const(f'color_{i}', ColorSort) for i in range(1, 5)]
    
    # Each house has a unique name and color
    solver.add(Distinct(names))
    solver.add(Distinct(colors))
    
    # Clue 1: The person whose favorite color is green is in the third house.
    solver.add(colors[2] == green)
    
    # Clue 2: Peter is in the first house.
    solver.add(names[0] == Peter)
    
    # Clue 3: There is one house between the person whose favorite color is red and the person who loves yellow.
    # We'll find the house indices for red and yellow and ensure |red_house - yellow_house| == 2
    red_house = Int('red_house')
    yellow_house = Int('yellow_house')
    solver.add(red_house >= 1, red_house <= 4)
    solver.add(yellow_house >= 1, yellow_house <= 4)
    for i in range(4):
        solver.add(If(colors[i] == red, red_house == i+1, True))
        solver.add(If(colors[i] == yellow, yellow_house == i+1, True))
    solver.add(Abs(red_house - yellow_house) == 2)
    
    # Clue 4: Arnold is directly left of Eric.
    # So Arnold's house + 1 = Eric's house
    arnold_house = Int('arnold_house')
    eric_house = Int('eric_house')
    solver.add(arnold_house >= 1, arnold_house <= 4)
    solver.add(eric_house >= 1, eric_house <= 4)
    for i in range(4):
        solver.add(If(names[i] == Arnold, arnold_house == i+1, True))
        solver.add(If(names[i] == Eric, eric_house == i+1, True))
    solver.add(eric_house == arnold_house + 1)
    
    # Clue 5: Eric is the person who loves yellow.
    # So for the house where name is Eric, color must be yellow
    for i in range(4):
        solver.add(If(names[i] == Eric, colors[i] == yellow, True))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare the result
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = str(model.eval(names[i]))
            color_val = str(model.eval(colors[i]))
            rows.append([house_num, name_val, color_val])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Color"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()