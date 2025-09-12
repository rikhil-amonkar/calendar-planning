import z3
import json

def main():
    # Define the houses
    n_houses = 5
    houses = list(range(1, n_houses+1))
    
    # Define attributes
    names = ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']
    foods = ['stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry']
    
    # Create Z3 variables for each attribute per house
    name_vars = [z3.Int(f"name_{i}") for i in houses]
    height_vars = [z3.Int(f"height_{i}") for i in houses]
    food_vars = [z3.Int(f"food_{i}") for i in houses]
    
    # Create solver
    solver = z3.Solver()
    
    # Constraint: All name variables must be between 0 and 4 (index of names)
    for var in name_vars:
        solver.add(z3.And(var >= 0, var < len(names)))
    
    # Constraint: All height variables must be between 0 and 4 (index of heights)
    for var in height_vars:
        solver.add(z3.And(var >= 0, var < len(heights)))
    
    # Constraint: All food variables must be between 0 and 4 (index of foods)
    for var in food_vars:
        solver.add(z3.And(var >= 0, var < len(foods)))
    
    # Constraint: All names are distinct
    solver.add(z3.Distinct(name_vars))
    
    # Constraint: All heights are distinct
    solver.add(z3.Distinct(height_vars))
    
    # Constraint: All foods are distinct
    solver.add(z3.Distinct(food_vars))
    
    # Map attribute values to indices for easier constraint writing
    name_to_idx = {name: idx for idx, name in enumerate(names)}
    height_to_idx = {height: idx for idx, height in enumerate(heights)}
    food_to_idx = {food: idx for idx, food in enumerate(foods)}
    
    # Clue 1: Alice is the person who is short.
    alice_idx = name_to_idx['Alice']
    short_idx = height_to_idx['short']
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == alice_idx, height_vars[i-1] == short_idx))
    
    # Clue 2: The person who is tall is in the third house.
    tall_idx = height_to_idx['tall']
    solver.add(height_vars[2] == tall_idx)
    
    # Clue 3: The person who has an average height is not in the second house.
    average_idx = height_to_idx['average']
    solver.add(height_vars[1] != average_idx)
    
    # Clue 4: The person who has an average height is somewhere to the left of the person who loves the stew.
    stew_idx = food_to_idx['stew']
    for i in houses:
        for j in houses:
            if i < j:
                solver.add(z3.Implies(
                    z3.And(height_vars[i-1] == average_idx, food_vars[j-1] == stew_idx),
                    i < j
                ))
    
    # Clue 5: The person who loves stir fry is Arnold.
    stir_fry_idx = food_to_idx['stir fry']
    arnold_idx = name_to_idx['Arnold']
    for i in houses:
        solver.add(z3.Implies(food_vars[i-1] == stir_fry_idx, name_vars[i-1] == arnold_idx))
    
    # Clue 6: The person who is a pizza lover is the person who is tall.
    pizza_idx = food_to_idx['pizza']
    for i in houses:
        solver.add(z3.Implies(food_vars[i-1] == pizza_idx, height_vars[i-1] == tall_idx))
    
    # Clue 7: Eric is the person who is tall.
    eric_idx = name_to_idx['Eric']
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == eric_idx, height_vars[i-1] == tall_idx))
    
    # Clue 8: Bob is somewhere to the right of Arnold.
    bob_idx = name_to_idx['Bob']
    for i in houses:
        for j in houses:
            if i < j:
                solver.add(z3.Implies(
                    z3.And(name_vars[i-1] == arnold_idx, name_vars[j-1] == bob_idx),
                    i < j
                ))
    
    # Clue 9: The person who loves eating grilled cheese is somewhere to the right of Eric.
    grilled_cheese_idx = food_to_idx['grilled cheese']
    for i in houses:
        for j in houses:
            if i < j:
                solver.add(z3.Implies(
                    z3.And(name_vars[i-1] == eric_idx, food_vars[j-1] == grilled_cheese_idx),
                    i < j
                ))
    
    # Clue 10: The person who is very short is somewhere to the left of Arnold.
    very_short_idx = height_to_idx['very short']
    for i in houses:
        for j in houses:
            if i < j:
                solver.add(z3.Implies(
                    z3.And(height_vars[i-1] == very_short_idx, name_vars[j-1] == arnold_idx),
                    i < j
                ))
    
    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Food"],
                "rows": []
            }
        }
        
        for house in houses:
            name_idx = model.evaluate(name_vars[house-1]).as_long()
            height_idx = model.evaluate(height_vars[house-1]).as_long()
            food_idx = model.evaluate(food_vars[house-1]).as_long()
            
            row = [
                str(house),
                names[name_idx],
                heights[height_idx],
                foods[food_idx]
            ]
            solution["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()