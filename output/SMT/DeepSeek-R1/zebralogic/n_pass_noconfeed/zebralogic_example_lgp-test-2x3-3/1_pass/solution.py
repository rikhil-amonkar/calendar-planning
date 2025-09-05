import z3
import json

def main():
    solver = z3.Solver()
    
    # Define attributes for each house
    houses = [1, 2]
    
    # Create Z3 variables for each attribute per house
    names = {h: z3.Int(f'name_{h}') for h in houses}
    foods = {h: z3.Int(f'food_{h}') for h in houses}
    mothers = {h: z3.Int(f'mother_{h}') for h in houses}
    
    # Define possible values
    name_values = {'Arnold': 0, 'Eric': 1}
    food_values = {'grilled cheese': 0, 'pizza': 1}
    mother_values = {'Holly': 0, 'Aniya': 1}
    
    # Add constraints: each attribute must be one of the possible values
    for h in houses:
        solver.add(z3.Or(names[h] == name_values['Arnold'], names[h] == name_values['Eric']))
        solver.add(z3.Or(foods[h] == food_values['grilled cheese'], foods[h] == food_values['pizza']))
        solver.add(z3.Or(mothers[h] == mother_values['Holly'], mothers[h] == mother_values['Aniya']))
    
    # All attributes are distinct across houses
    solver.add(z3.Distinct([names[h] for h in houses]))
    solver.add(z3.Distinct([foods[h] for h in houses]))
    solver.add(z3.Distinct([mothers[h] for h in houses]))
    
    # Clue 1: Grilled cheese is directly left of pizza
    solver.add(foods[1] == food_values['grilled cheese'])
    solver.add(foods[2] == food_values['pizza'])
    
    # Clue 2: Arnold is not in second house
    solver.add(names[1] == name_values['Arnold'])
    
    # Clue 3: Arnold's mother is Holly
    solver.add(mothers[1] == mother_values['Holly'])
    
    # Check solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create reverse mappings for value to string
        rev_name = {v: k for k, v in name_values.items()}
        rev_food = {v: k for k, v in food_values.items()}
        rev_mother = {v: k for k, v in mother_values.items()}
        
        # Build result rows
        rows = []
        for h in houses:
            name_val = model.evaluate(names[h]).as_long()
            food_val = model.evaluate(foods[h]).as_long()
            mother_val = model.evaluate(mothers[h]).as_long()
            
            rows.append([
                str(h),
                rev_name[name_val],
                rev_food[food_val],
                rev_mother[mother_val]
            ])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Mother"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()