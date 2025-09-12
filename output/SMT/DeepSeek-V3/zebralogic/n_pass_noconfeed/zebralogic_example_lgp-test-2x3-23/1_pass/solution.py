import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the houses
    houses = [1, 2]
    
    # Define the attributes
    names = ['Eric', 'Arnold']
    children = ['Bella', 'Fred']
    foods = ['grilled cheese', 'pizza']
    
    # Create variables for each attribute per house
    name_vars = {h: z3.Int(f'name_{h}') for h in houses}
    child_vars = {h: z3.Int(f'child_{h}') for h in houses}
    food_vars = {h: z3.Int(f'food_{h}') for h in houses}
    
    # Define the domain for each attribute (0-indexed)
    name_domain = {0: 'Eric', 1: 'Arnold'}
    child_domain = {0: 'Bella', 1: 'Fred'}
    food_domain = {0: 'grilled cheese', 1: 'pizza'}
    
    # Constraint: All attributes must be within their domain
    for h in houses:
        solver.add(z3.And(name_vars[h] >= 0, name_vars[h] < len(names)))
        solver.add(z3.And(child_vars[h] >= 0, child_vars[h] < len(children)))
        solver.add(z3.And(food_vars[h] >= 0, food_vars[h] < len(foods)))
    
    # Constraint: All attributes are unique within their category
    solver.add(z3.Distinct([name_vars[h] for h in houses]))
    solver.add(z3.Distinct([child_vars[h] for h in houses]))
    solver.add(z3.Distinct([food_vars[h] for h in houses]))
    
    # Clue 1: The person who is a pizza lover is Arnold.
    # Arnold is at index 1 in names, pizza is at index 1 in foods
    for h in houses:
        solver.add(z3.Implies(food_vars[h] == 1, name_vars[h] == 1))
    
    # Clue 2: The person who loves eating grilled cheese is directly left of the person's child is named Fred.
    # grilled cheese is at index 0 in foods, Fred is at index 1 in children
    # House 1 is left of house 2
    solver.add(z3.Or(
        z3.And(food_vars[1] == 0, child_vars[2] == 1),  # grilled cheese in house 1, Fred in house 2
        z3.And(food_vars[2] == 0, child_vars[1] == 1)   # grilled cheese in house 2, Fred in house 1 (but this can't be "directly left")
    ))
    # Since house 2 can't be left of anything, we need to ensure the correct interpretation
    # The person with grilled cheese must be in house 1, and Fred must be in house 2
    solver.add(food_vars[1] == 0)
    solver.add(child_vars[2] == 1)
    
    # Check if the problem is satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare the solution
        rows = []
        for h in houses:
            name_val = name_domain[model[name_vars[h]].as_long()]
            child_val = child_domain[model[child_vars[h]].as_long()]
            food_val = food_domain[model[food_vars[h]].as_long()]
            rows.append([str(h), name_val, child_val, food_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Children", "Food"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()