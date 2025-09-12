import z3
import json

def main():
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2]
    
    # Define attributes
    names = ['Eric', 'Arnold']
    foods = ['pizza', 'grilled cheese']
    
    # Create variables for each attribute per house
    name_vars = {}
    food_vars = {}
    
    for house in houses:
        name_vars[house] = z3.Int(f'name_{house}')
        food_vars[house] = z3.Int(f'food_{house}')
    
    # Constraint: All attributes must be within their domain
    for house in houses:
        solver.add(z3.And(name_vars[house] >= 0, name_vars[house] < len(names)))
        solver.add(z3.And(food_vars[house] >= 0, food_vars[house] < len(foods)))
    
    # Constraint: All attributes are distinct within their category
    solver.add(z3.Distinct([name_vars[house] for house in houses]))
    solver.add(z3.Distinct([food_vars[house] for house in houses]))
    
    # Clue 1: The person who is a pizza lover is in the second house.
    pizza_index = foods.index('pizza')
    solver.add(food_vars[2] == pizza_index)
    
    # Clue 2: Arnold is not in the first house.
    arnold_index = names.index('Arnold')
    solver.add(name_vars[1] != arnold_index)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        header = ["House", "Name", "Food"]
        rows = []
        
        for house in sorted(houses):
            name_index = model.evaluate(name_vars[house]).as_long()
            food_index = model.evaluate(food_vars[house]).as_long()
            
            row = [
                str(house),
                names[name_index],
                foods[food_index]
            ]
            rows.append(row)
        
        # Create JSON output
        solution = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()