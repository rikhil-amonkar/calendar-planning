from z3 import *

def main():
    # Create enums for attributes
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
    
    # Create variables for each house
    house1_name = Const('house1_name', Name)
    house1_birthday = Const('house1_birthday', Birthday)
    house1_color = Const('house1_color', Color)
    
    house2_name = Const('house2_name', Name)
    house2_birthday = Const('house2_birthday', Birthday)
    house2_color = Const('house2_color', Color)
    
    s = Solver()
    
    # All names, birthdays, colors are unique
    s.add(Distinct(house1_name, house2_name))
    s.add(Distinct(house1_birthday, house2_birthday))
    s.add(Distinct(house1_color, house2_color))
    
    # Clue 1: Eric is the person who loves yellow.
    s.add(ForAll([x], Implies(house1_name == Name.Eric, house1_color == Color.yellow)))
    s.add(ForAll([x], Implies(house2_name == Name.Eric, house2_color == Color.yellow)))
    
    # Clue 2: The person whose birthday is in April is in the first house.
    s.add(house1_birthday == Birthday.april)
    
    # Clue 3: The person who loves yellow is not in the first house.
    s.add(house1_color != Color.yellow)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        
        # Function to convert enum to string
        def name_str(val):
            if m.eval(val) == Name.Eric:
                return "Eric"
            else:
                return "Arnold"
                
        def birthday_str(val):
            if m.eval(val) == Birthday.april:
                return "april"
            else:
                return "sept"
                
        def color_str(val):
            if m.eval(val) == Color.yellow:
                return "yellow"
            else:
                return "red"
                
        house1 = [
            "1",
            name_str(house1_name),
            birthday_str(house1_birthday),
            color_str(house1_color)
        ]
        
        house2 = [
            "2",
            name_str(house2_name),
            birthday_str(house2_birthday),
            color_str(house2_color)
        ]
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Color"],
                "rows": [house1, house2]
            }
        }
        
        import json
        print(json.dumps(solution))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()