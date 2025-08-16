from z3 import *
import json

def main():
    # We will assign each house a name and a food.
    # For names, we let: 0 represent "Eric", 1 represent "Arnold"
    # For food, we let: 0 represent "grilled cheese", 1 represent "pizza"
    # There are two houses: house1 and house2.
    
    # Create Z3 integer variables for each house's name and food.
    house1_name = Int("house1_name")
    house1_food = Int("house1_food")
    house2_name = Int("house2_name")
    house2_food = Int("house2_food")
    
    solver = Solver()
    
    # Each variable is either 0 or 1.
    solver.add(Or(house1_name == 0, house1_name == 1))
    solver.add(Or(house2_name == 0, house2_name == 1))
    solver.add(Or(house1_food == 0, house1_food == 1))
    solver.add(Or(house2_food == 0, house2_food == 1))
    
    # Ensure that each house has a unique person and unique food.
    solver.add(Distinct(house1_name, house2_name))
    solver.add(Distinct(house1_food, house2_food))
    
    # Clue 1: The person who is a pizza lover is in the second house.
    # With our encoding, pizza is represented by 1.
    solver.add(house2_food == 1)
    
    # Clue 2: Arnold is not in the first house.
    # With our encoding, Arnold is represented by 1.
    solver.add(house1_name != 1)
    
    if solver.check() == sat:
        model = solver.model()
        name_map = {0: "Eric", 1: "Arnold"}
        food_map = {0: "grilled cheese", 1: "pizza"}
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Food"],
                "rows": [
                    ["1", name_map[model[house1_name].as_long()], food_map[model[house1_food].as_long()]],
                    ["2", name_map[model[house2_name].as_long()], food_map[model[house2_food].as_long()]]
                ]
            }
        }
        print(json.dumps(solution))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()