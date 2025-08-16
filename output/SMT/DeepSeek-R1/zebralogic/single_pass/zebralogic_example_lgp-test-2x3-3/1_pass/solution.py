from z3 import *
import json

def main():
    # Define the enums for attributes
    Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    Food, (grilled_cheese, pizza) = EnumSort('Food', ['grilled cheese', 'pizza'])
    Mother, (Holly, Aniya) = EnumSort('Mother', ['Holly', 'Aniya'])
    
    # Create variables for each house's attributes
    house1_name = Const('house1_name', Name)
    house1_food = Const('house1_food', Food)
    house1_mother = Const('house1_mother', Mother)
    
    house2_name = Const('house2_name', Name)
    house2_food = Const('house2_food', Food)
    house2_mother = Const('house2_mother', Mother)
    
    s = Solver()
    
    # Clue 1: grilled cheese is directly left of pizza
    s.add(house1_food == grilled_cheese)
    s.add(house2_food == pizza)
    
    # Clue 2: Arnold is not in the second house
    s.add(house1_name == Arnold)
    
    # Clue 3: Arnold's mother is Holly
    s.add(house1_mother == Holly)
    
    # Ensure uniqueness across houses
    s.add(Distinct(house1_name, house2_name))
    s.add(Distinct(house1_food, house2_food))
    s.add(Distinct(house1_mother, house2_mother))
    
    if s.check() == sat:
        m = s.model()
        # Extract values for House 1
        h1_name = m.eval(house1_name)
        h1_food = m.eval(house1_food)
        h1_mother = m.eval(house1_mother)
        # Extract values for House 2
        h2_name = m.eval(house2_name)
        h2_food = m.eval(house2_food)
        h2_mother = m.eval(house2_mother)
        
        # Prepare rows for the solution
        rows = [
            ["1", str(h1_name), str(h1_food), str(h1_mother)],
            ["2", str(h2_name), str(h2_food), str(h2_mother)]
        ]
        
        # Construct the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Food", "Mother"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()