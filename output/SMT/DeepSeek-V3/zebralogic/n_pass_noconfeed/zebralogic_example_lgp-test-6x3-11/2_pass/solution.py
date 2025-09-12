from z3 import *
import json

def main():
    # Define the number of houses
    n = 6
    houses = range(1, n+1)
    
    # Create solver
    solver = Solver()
    
    # Define variables for each attribute
    name = [Int(f"name_{i}") for i in houses]
    hair_color = [Int(f"hair_color_{i}") for i in houses]
    height = [Int(f"height_{i}") for i in houses]
    
    # Define domains for each attribute
    names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
    name_domain = {name: idx for idx, name in enumerate(names)}
    
    hair_colors = ["auburn", "blonde", "brown", "black", "red", "gray"]
    hair_color_domain = {color: idx for idx, color in enumerate(hair_colors)}
    
    heights = ["very tall", "average", "very short", "tall", "super tall", "short"]
    height_domain = {height: idx for idx, height in enumerate(heights)}
    
    # Constraint: All attributes are within their domains
    for i in houses:
        solver.add(And(name[i-1] >= 0, name[i-1] < len(names)))
        solver.add(And(hair_color[i-1] >= 0, hair_color[i-1] < len(hair_colors)))
        solver.add(And(height[i-1] >= 0, height[i-1] < len(heights)))
    
    # Constraint: All attributes are distinct within their category
    solver.add(Distinct(name))
    solver.add(Distinct(hair_color))
    solver.add(Distinct(height))
    
    # Clue 1: The person who has blonde hair is directly left of Bob.
    blonde_idx = hair_color_domain["blonde"]
    bob_idx = name_domain["Bob"]
    for i in range(1, n):
        solver.add(Implies(hair_color[i-1] == blonde_idx, name[i] == bob_idx))
    
    # Clue 2: Alice is in the fourth house.
    alice_idx = name_domain["Alice"]
    solver.add(name[3] == alice_idx)
    
    # Clue 3: The person who is short is Arnold.
    short_idx = height_domain["short"]
    arnold_idx = name_domain["Arnold"]
    for i in houses:
        solver.add(Implies(height[i-1] == short_idx, name[i-1] == arnold_idx))
    
    # Clue 4: The person who is tall is in the sixth house.
    tall_idx = height_domain["tall"]
    solver.add(height[5] == tall_idx)
    
    # Clue 5: The person who has black hair is not in the fourth house.
    black_idx = hair_color_domain["black"]
    solver.add(hair_color[3] != black_idx)
    
    # Clue 6: The person who has red hair is Eric.
    red_idx = hair_color_domain["red"]
    eric_idx = name_domain["Eric"]
    for i in houses:
        solver.add(Implies(hair_color[i-1] == red_idx, name[i-1] == eric_idx))
    
    # Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
    super_tall_idx = height_domain["super tall"]
    average_idx = height_domain["average"]
    # Create a constraint that super tall is to the right of average
    for i in houses:
        for j in houses:
            if j >= i:  # j is to the right of i
                continue
            # If height[i] is average, then super tall must be in position j where j > i
            solver.add(Implies(height[i-1] == average_idx, 
                              Or([height[j-1] == super_tall_idx for j in range(i+1, n+1)])))
    
    # Clue 8: The person who has blonde hair is Carol.
    carol_idx = name_domain["Carol"]
    for i in houses:
        solver.add(Implies(hair_color[i-1] == blonde_idx, name[i-1] == carol_idx))
    
    # Clue 9: There is one house between the person who has gray hair and the person who has red hair.
    gray_idx = hair_color_domain["gray"]
    red_idx = hair_color_domain["red"]
    gray_red_positions = []
    for i in range(1, n-1):
        gray_red_positions.append(And(hair_color[i-1] == gray_idx, hair_color[i+1] == red_idx))
        gray_red_positions.append(And(hair_color[i-1] == red_idx, hair_color[i+1] == gray_idx))
    solver.add(Or(gray_red_positions))
    
    # Clue 10: The person who is very short is in the fifth house.
    very_short_idx = height_domain["very short"]
    solver.add(height[4] == very_short_idx)
    
    # Clue 11: Bob is the person who has brown hair.
    brown_idx = hair_color_domain["brown"]
    for i in houses:
        solver.add(Implies(name[i-1] == bob_idx, hair_color[i-1] == brown_idx))
    
    # Clue 12: The person who has gray hair is in the third house.
    solver.add(hair_color[2] == gray_idx)
    
    # Clue 13: The person who has blonde hair is the person who is very tall.
    very_tall_idx = height_domain["very tall"]
    for i in houses:
        solver.add(Implies(hair_color[i-1] == blonde_idx, height[i-1] == very_tall_idx))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "Height"],
                "rows": []
            }
        }
        
        # Extract values from the model
        for i in houses:
            house_num = str(i)
            name_val = names[model.evaluate(name[i-1]).as_long()]
            hair_color_val = hair_colors[model.evaluate(hair_color[i-1]).as_long()]
            height_val = heights[model.evaluate(height[i-1]).as_long()]
            
            solution["solution"]["rows"].append([house_num, name_val, hair_color_val, height_val])
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()