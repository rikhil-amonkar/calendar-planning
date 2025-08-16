import json
from z3 import *

def main():
    # Define the name datatype
    Name = Datatype('Name')
    Name.declare('Peter')
    Name.declare('Arnold')
    Name.declare('Alice')
    Name.declare('Eric')
    Name = Name.create()
    
    # Define the color datatype
    Color = Datatype('Color')
    Color.declare('yellow')
    Color.declare('green')
    Color.declare('red')
    Color.declare('white')
    Color = Color.create()
    
    # Create variables for names and colors of each house
    names = [Const(f'n{i}', Name) for i in range(1,5)]
    colors = [Const(f'c{i}', Color) for i in range(1,5)]
    
    s = Solver()
    
    # All names are distinct
    s.add(Distinct(names))
    # All colors are distinct
    s.add(Distinct(colors))
    
    # Clue 1: Green is in the third house
    s.add(colors[2] == Color.green)
    
    # Clue 2: Peter is in the first house
    s.add(names[0] == Name.Peter)
    
    # Clue 3: One house between red and yellow
    s.add(Or(
        And(colors[0] == Color.red, colors[2] == Color.yellow),
        And(colors[0] == Color.yellow, colors[2] == Color.red),
        And(colors[1] == Color.red, colors[3] == Color.yellow),
        And(colors[1] == Color.yellow, colors[3] == Color.red)
    ))
    
    # Clue 4: Arnold is directly left of Eric
    s.add(Or(
        And(names[0] == Name.Arnold, names[1] == Name.Eric),
        And(names[1] == Name.Arnold, names[2] == Name.Eric),
        And(names[2] == Name.Arnold, names[3] == Name.Eric)
    ))
    
    # Clue 5: Eric loves yellow
    for i in range(4):
        s.add(Implies(names[i] == Name.Eric, colors[i] == Color.yellow))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = model.eval(names[i])
            color_val = model.eval(colors[i])
            name_str = str(name_val)
            color_str = str(color_val)
            rows.append([house_num, name_str, color_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Color"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()