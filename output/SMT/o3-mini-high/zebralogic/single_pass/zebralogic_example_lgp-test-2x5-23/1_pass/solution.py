from z3 import *
import json

def main():
    solver = Solver()

    # We have 2 houses, indexed as 0 (House 1) and 1 (House 2).
    # We map each attribute to an integer domain {0, 1}:
    # Name: 0 -> "Arnold", 1 -> "Eric"
    # Education: 0 -> "associate", 1 -> "high school"
    # Height: 0 -> "short", 1 -> "very short"
    # Food: 0 -> "grilled cheese", 1 -> "pizza"
    # Drink: 0 -> "tea", 1 -> "water"
    #
    # Clues:
    # 1. The person who is very short (height == 1) is the person who is a pizza lover (food == 1).
    # 2. The person who loves eating grilled cheese (food == 0) is in the second house (House 2, index 1).
    # 3. The person with a high school diploma (education == 1) is the person who is a pizza lover (food == 1).
    # 4. The tea drinker (drink == 0) is the person who loves eating grilled cheese (food == 0).
    # 5. Arnold (name == 0) is the person who is a pizza lover (food == 1).
    
    # Create list variables for each attribute for both houses
    houses = 2
    names   = [Int(f"name_{i}") for i in range(houses)]
    educ    = [Int(f"educ_{i}") for i in range(houses)]
    height  = [Int(f"height_{i}") for i in range(houses)]
    food    = [Int(f"food_{i}") for i in range(houses)]
    drink   = [Int(f"drink_{i}") for i in range(houses)]
    
    # Each variable can only be 0 or 1.
    for i in range(houses):
        solver.add(Or(names[i] == 0, names[i] == 1))
        solver.add(Or(educ[i]  == 0, educ[i]  == 1))
        solver.add(Or(height[i]== 0, height[i]== 1))
        solver.add(Or(food[i]  == 0, food[i]  == 1))
        solver.add(Or(drink[i] == 0, drink[i] == 1))
        
    # Uniqueness constraints: values for the same attribute must be different across houses.
    solver.add(Distinct(names[0], names[1]))
    solver.add(Distinct(educ[0], educ[1]))
    solver.add(Distinct(height[0], height[1]))
    solver.add(Distinct(food[0], food[1]))
    solver.add(Distinct(drink[0], drink[1]))
    
    # Clue 2: The person who loves eating grilled cheese is in the second house.
    # grilled cheese is represented by 0.
    solver.add(food[1] == 0)
    
    # Clue 1: Very short <-> Pizza lover.
    # Clue 3: High school <-> Pizza lover.
    for i in range(houses):
        solver.add(Implies(food[i] == 1, height[i] == 1))
        solver.add(Implies(height[i] == 1, food[i] == 1))
        solver.add(Implies(food[i] == 1, educ[i] == 1))
        solver.add(Implies(educ[i] == 1, food[i] == 1))
    
    # Clue 4: The tea drinker is the person who loves grilled cheese.
    # tea is represented by 0.
    for i in range(houses):
        solver.add(Implies(food[i] == 0, drink[i] == 0))
        solver.add(Implies(drink[i] == 0, food[i] == 0))
    
    # Clue 5: Arnold is the person who is a pizza lover.
    # Name: Arnold is 0, and pizza is 1.
    for i in range(houses):
        solver.add(Implies(names[i] == 0, food[i] == 1))
        solver.add(Implies(food[i] == 1, names[i] == 0))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        
        # Mapping of integer values to their string representations.
        name_map   = {0: "Arnold", 1: "Eric"}
        educ_map   = {0: "associate", 1: "high school"}
        height_map = {0: "short", 1: "very short"}
        food_map   = {0: "grilled cheese", 1: "pizza"}
        drink_map  = {0: "tea", 1: "water"}
        
        rows = []
        # House indices: 0->House "1", 1->House "2" (left-to-right order)
        for i in range(houses):
            house_number = str(i+1)
            person_name  = name_map[model[names[i]].as_long()]
            education    = educ_map[model[educ[i]].as_long()]
            height_val   = height_map[model[height[i]].as_long()]
            food_val     = food_map[model[food[i]].as_long()]
            drink_val    = drink_map[model[drink[i]].as_long()]
            rows.append([house_number, person_name, education, height_val, food_val, drink_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                "rows": rows
            }
        }
        
        # Print the final solution in valid JSON format.
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()