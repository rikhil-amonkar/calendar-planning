import z3
import json

def main():
    # Define the houses
    n_houses = 5
    houses = list(range(1, n_houses+1))
    
    # Define attributes in the correct order
    names = ['Peter', 'Arnold', 'Bob', 'Alice', 'Eric']
    heights = ['very short', 'short', 'average', 'tall', 'very tall']
    foods = ['spaghetti', 'stir fry', 'grilled cheese', 'pizza', 'stew']
    
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
    for i in range(n_houses):
        solver.add(z3.Implies(name_vars[i] == alice_idx, height_vars[i] == short_idx))
    
    # Clue 2: The person who is tall is in the third house.
    tall_idx = height_to_idx['tall']
    solver.add(height_vars[2] == tall_idx)  # House 3 has index 2
    
    # Clue 3: The person who has an average height is not in the second house.
    average_idx = height_to_idx['average']
    solver.add(height_vars[1] != average_idx)  # House 2 has index 1
    
    # Clue 4: The person who has an average height is somewhere to the left of the person who loves the stew.
    stew_idx = food_to_idx['stew']
    # Create a constraint that there exists some house i with average height and some house j > i with stew
    solver.add(z3.Or([
        z3.And(height_vars[i] == average_idx, food_vars[j] == stew_idx, i < j)
        for i in range(n_houses) for j in range(n_houses) if i < j
    ]))
    
    # Clue 5: The person who loves stir fry is Arnold.
    stir_fry_idx = food_to_idx['stir fry']
    arnold_idx = name_to_idx['Arnold']
    for i in range(n_houses):
        solver.add(z3.Implies(food_vars[i] == stir_fry_idx, name_vars[i] == arnold_idx))
    
    # Clue 6: The person who is a pizza lover is the person who is tall.
    pizza_idx = food_to_idx['pizza']
    for i in range(n_houses):
        solver.add(z3.Implies(food_vars[i] == pizza_idx, height_vars[i] == tall_idx))
    
    # Clue 7: Eric is the person who is tall.
    eric_idx = name_to_idx['Eric']
    for i in range(n_houses):
        solver.add(z3.Implies(name_vars[i] == eric_idx, height_vars[i] == tall_idx))
    
    # Clue 8: Bob is somewhere to the right of Arnold.
    bob_idx = name_to_idx['Bob']
    # Create a constraint that Arnold is in some house i and Bob is in some house j > i
    solver.add(z3.Or([
        z3.And(name_vars[i] == arnold_idx, name_vars[j] == bob_idx, i < j)
        for i in range(n_houses) for j in range(n_houses) if i < j
    ]))
    
    # Clue 9: The person who loves eating grilled cheese is somewhere to the right of Eric.
    grilled_cheese_idx = food_to_idx['grilled cheese']
    # Create a constraint that Eric is in some house i and grilled cheese is in some house j > i
    solver.add(z3.Or([
        z3.And(name_vars[i] == eric_idx, food_vars[j] == grilled_cheese_idx, i < j)
        for i in range(n_houses) for j in range(n_houses) if i < j
    ]))
    
    # Clue 10: The person who is very short is somewhere to the left of Arnold.
    very_short_idx = height_to_idx['very short']
    # Create a constraint that very short is in some house i and Arnold is in some house j > i
    solver.add(z3.Or([
        z3.And(height_vars[i] == very_short_idx, name_vars[j] == arnold_idx, i < j)
        for i in range(n_houses) for j in range(n_houses) if i < j
    ]))
    
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