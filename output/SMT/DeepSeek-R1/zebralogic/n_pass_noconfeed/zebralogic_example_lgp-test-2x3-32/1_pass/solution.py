import json
from z3 import *

def main():
    # Define the sorts for attributes
    Name = Datatype('Name')
    Name.declare('Eric')
    Name.declare('Arnold')
    Name = Name.create()
    
    Birthday = Datatype('Birthday')
    Birthday.declare('april')
    Birthday.declare('sept')
    Birthday = Birthday.create()
    
    Color = Datatype('Color')
    Color.declare('yellow')
    Color.declare('red')
    Color = Color.create()
    
    # Create variables for each house's attributes
    h1_name = Const('h1_name', Name)
    h1_birthday = Const('h1_birthday', Birthday)
    h1_color = Const('h1_color', Color)
    
    h2_name = Const('h2_name', Name)
    h2_birthday = Const('h2_birthday', Birthday)
    h2_color = Const('h2_color', Color)
    
    solver = Solver()
    
    # Each attribute must be unique across houses
    solver.add(Distinct(h1_name, h2_name))
    solver.add(Distinct(h1_birthday, h2_birthday))
    solver.add(Distinct(h1_color, h2_color))
    
    # Clue 1: Eric loves yellow
    solver.add(Implies(h1_name == Name.Eric, h1_color == Color.yellow))
    solver.add(Implies(h2_name == Name.Eric, h2_color == Color.yellow))
    
    # Clue 2: April birthday in first house
    solver.add(h1_birthday == Birthday.april)
    
    # Clue 3: Yellow lover not in first house
    solver.add(h1_color != Color.yellow)
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Mapping from Z3 values to strings
        name_map = {Name.Eric: "Eric", Name.Arnold: "Arnold"}
        birthday_map = {Birthday.april: "april", Birthday.sept: "sept"}
        color_map = {Color.yellow: "yellow", Color.red: "red"}
        
        # Extract values from model
        house1 = [
            "1",
            name_map[model.eval(h1_name)],
            birthday_map[model.eval(h1_birthday)],
            color_map[model.eval(h1_color)]
        ]
        
        house2 = [
            "2",
            name_map[model.eval(h2_name)],
            birthday_map[model.eval(h2_birthday)],
            color_map[model.eval(h2_color)]
        ]
        
        # Create solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Color"],
                "rows": [house1, house2]
            }
        }
        
        # Output JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()