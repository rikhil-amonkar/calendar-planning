import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    styles = ['victorian', 'ranch', 'colonial', 'craftsman']
    
    # Create variables for each attribute per house
    name_vars = {h: z3.Int(f'name_{h}') for h in houses}
    style_vars = {h: z3.Int(f'style_{h}') for h in houses}
    
    # Create constraints for name variables (0-3)
    for h in houses:
        solver.add(z3.And(name_vars[h] >= 0, name_vars[h] < len(names)))
    
    # Create constraints for style variables (0-3)
    for h in houses:
        solver.add(z3.And(style_vars[h] >= 0, style_vars[h] < len(styles)))
    
    # All names are distinct
    solver.add(z3.Distinct([name_vars[h] for h in houses]))
    
    # All styles are distinct
    solver.add(z3.Distinct([style_vars[h] for h in houses]))
    
    # Clue 1: Eric is the person in a Craftsman-style house
    eric_index = names.index('Eric')
    craftsman_index = styles.index('craftsman')
    for h in houses:
        solver.add(z3.Implies(name_vars[h] == eric_index, style_vars[h] == craftsman_index))
    
    # Clue 2: The person in a ranch-style home is directly left of the person residing in a Victorian house
    ranch_index = styles.index('ranch')
    victorian_index = styles.index('victorian')
    for h in range(1, 4):  # Houses 1, 2, 3 (house 4 has no right neighbor)
        solver.add(z3.Implies(style_vars[h] == ranch_index, style_vars[h+1] == victorian_index))
    
    # Clue 3: Eric is in the third house
    solver.add(name_vars[3] == eric_index)
    
    # Clue 4: Arnold is in the fourth house
    arnold_index = names.index('Arnold')
    solver.add(name_vars[4] == arnold_index)
    
    # Clue 5: The person residing in a Victorian house is Alice
    alice_index = names.index('Alice')
    for h in houses:
        solver.add(z3.Implies(style_vars[h] == victorian_index, name_vars[h] == alice_index))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in sorted(houses):
            name_val = model.eval(name_vars[house]).as_long()
            style_val = model.eval(style_vars[house]).as_long()
            
            row = [
                str(house),
                names[name_val],
                styles[style_val]
            ]
            solution["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()