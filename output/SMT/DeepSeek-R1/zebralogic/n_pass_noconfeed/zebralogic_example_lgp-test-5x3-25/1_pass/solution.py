from z3 import *
import json

def main():
    # Define the attributes
    names = ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']
    foods = ['stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry']
    
    # Create solver instance
    solver = Solver()
    
    # Create variables for each house's attributes
    name_vars = [Int(f'name_{i}') for i in range(1, 6)]
    height_vars = [Int(f'height_{i}') for i in range(1, 6)]
    food_vars = [Int(f'food_{i}') for i in range(1, 6)]
    
    # Create domain constraints for each variable
    for i in range(5):
        solver.add(name_vars[i] >= 0, name_vars[i] < 5)
        solver.add(height_vars[i] >= 0, height_vars[i] < 5)
        solver.add(food_vars[i] >= 0, food_vars[i] < 5)
    
    # All attributes must be distinct per category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(height_vars))
    solver.add(Distinct(food_vars))
    
    # Create mapping from index to attribute value
    name_map = {i: name for i, name in enumerate(names)}
    height_map = {i: height for i, height in enumerate(heights)}
    food_map = {i: food for i, food in enumerate(foods)}
    
    # Add clues as constraints
    # Clue 1: Alice is short
    alice_idx = names.index('Alice')
    short_idx = heights.index('short')
    solver.add(Or([And(name_vars[i] == alice_idx, height_vars[i] == short_idx) for i in range(5)]))
    
    # Clue 2: Tall person is in house 3 (index 2)
    tall_idx = heights.index('tall')
    solver.add(height_vars[2] == tall_idx)
    
    # Clue 3: Average height not in house 2
    avg_idx = heights.index('average')
    solver.add(height_vars[1] != avg_idx)
    
    # Clue 4: Average height left of stew lover
    stew_idx = foods.index('stew')
    solver.add(Or([And(height_vars[i] == avg_idx, food_vars[j] == stew_idx, i < j) for i in range(5) for j in range(5)]))
    
    # Clue 5: Stir fry is Arnold
    arnold_idx = names.index('Arnold')
    stir_fry_idx = foods.index('stir fry')
    solver.add(Or([And(name_vars[i] == arnold_idx, food_vars[i] == stir_fry_idx) for i in range(5)]))
    
    # Clue 6: Pizza lover is tall
    pizza_idx = foods.index('pizza')
    solver.add(Or([And(height_vars[i] == tall_idx, food_vars[i] == pizza_idx) for i in range(5)]))
    
    # Clue 7: Eric is tall
    eric_idx = names.index('Eric')
    solver.add(Or([And(name_vars[i] == eric_idx, height_vars[i] == tall_idx) for i in range(5)]))
    
    # Clue 8: Bob is right of Arnold
    bob_idx = names.index('Bob')
    solver.add(Or([And(name_vars[i] == arnold_idx, name_vars[j] == bob_idx, i < j) for i in range(5) for j in range(5)]))
    
    # Clue 9: Grilled cheese right of Eric
    grilled_cheese_idx = foods.index('grilled cheese')
    solver.add(Or([And(name_vars[i] == eric_idx, food_vars[j] == grilled_cheese_idx, i < j) for i in range(5) for j in range(5)]))
    
    # Clue 10: Very short left of Arnold
    very_short_idx = heights.index('very short')
    solver.add(Or([And(height_vars[i] == very_short_idx, name_vars[j] == arnold_idx, i < j) for i in range(5) for j in range(5)]))
    
    # Check satisfiability and get model
    if solver.check() == sat:
        model = solver.model()
        
        # Build solution matrix
        rows = []
        for i in range(5):
            house_num = str(i + 1)
            name_val = name_map[model.evaluate(name_vars[i]).as_long()]
            height_val = height_map[model.evaluate(height_vars[i]).as_long()]
            food_val = food_map[model.evaluate(food_vars[i]).as_long()]
            rows.append([house_num, name_val, height_val, food_val])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Food"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()