import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the attributes
    names = ['Eric', 'Arnold']
    birthdays = ['sept', 'april']
    colors = ['yellow', 'red']
    
    # Create variables for each house's attributes
    house1_name = z3.Int('house1_name')
    house1_birthday = z3.Int('house1_birthday')
    house1_color = z3.Int('house1_color')
    
    house2_name = z3.Int('house2_name')
    house2_birthday = z3.Int('house2_birthday')
    house2_color = z3.Int('house2_color')
    
    # Domain constraints for house 1
    solver.add(z3.And(house1_name >= 0, house1_name < len(names)))
    solver.add(z3.And(house1_birthday >= 0, house1_birthday < len(birthdays)))
    solver.add(z3.And(house1_color >= 0, house1_color < len(colors)))
    
    # Domain constraints for house 2
    solver.add(z3.And(house2_name >= 0, house2_name < len(names)))
    solver.add(z3.And(house2_birthday >= 0, house2_birthday < len(birthdays)))
    solver.add(z3.And(house2_color >= 0, house2_color < len(colors)))
    
    # All attributes must be unique within their category
    solver.add(house1_name != house2_name)
    solver.add(house1_birthday != house2_birthday)
    solver.add(house1_color != house2_color)
    
    # Clue 1: Eric is the person who loves yellow
    # Eric has index 0, yellow has index 0
    solver.add(z3.Implies(house1_name == 0, house1_color == 0))
    solver.add(z3.Implies(house2_name == 0, house2_color == 0))
    
    # Clue 2: The person whose birthday is in April is in the first house
    # april has index 1
    solver.add(house1_birthday == 1)
    
    # Clue 3: The person who loves yellow is not in the first house
    # yellow has index 0
    solver.add(house1_color != 0)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract values from the model
        h1_name_idx = model[house1_name].as_long()
        h1_bday_idx = model[house1_birthday].as_long()
        h1_color_idx = model[house1_color].as_long()
        
        h2_name_idx = model[house2_name].as_long()
        h2_bday_idx = model[house2_birthday].as_long()
        h2_color_idx = model[house2_color].as_long()
        
        # Create solution rows
        rows = [
            ["1", names[h1_name_idx], birthdays[h1_bday_idx], colors[h1_color_idx]],
            ["2", names[h2_name_idx], birthdays[h2_bday_idx], colors[h2_color_idx]]
        ]
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Color"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()