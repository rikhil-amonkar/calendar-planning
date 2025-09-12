import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [0, 1, 2, 3]  # Using 0-based indexing for easier array access
    
    # Define attributes
    names = ['Eric', 'Arnold', 'Alice', 'Peter']
    styles = ['craftsman', 'colonial', 'ranch', 'victorian']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{h}') for h in range(4)]
    style_vars = [z3.Int(f'style_{h}') for h in range(4)]
    
    # Constraint: All name variables must be between 0 and 3 (indexes of names)
    for n in name_vars:
        solver.add(z3.And(n >= 0, n <= 3))
    
    # Constraint: All style variables must be between 0 and 3 (indexes of styles)
    for s in style_vars:
        solver.add(z3.And(s >= 0, s <= 3))
    
    # Constraint: All names are distinct
    solver.add(z3.Distinct(name_vars))
    
    # Constraint: All styles are distinct
    solver.add(z3.Distinct(style_vars))
    
    # Clue 1: Alice is in the second house
    # Alice is at index 2 in names list, second house is index 1 (0-based)
    solver.add(name_vars[1] == 2)
    
    # Clue 2: The person residing in a Victorian house is directly left of Peter
    # Victorian is at index 3 in styles list, Peter is at index 3 in names list
    for i in range(3):  # Check houses 0-2 (since Victorian must be directly left)
        solver.add(z3.Implies(style_vars[i] == 3, name_vars[i+1] == 3))
    
    # Clue 3: Peter is somewhere to the right of the person in a ranch-style home
    # Ranch is at index 2 in styles list, Peter is at index 3 in names list
    # This means ranch house position < Peter house position
    ranch_pos = z3.Int('ranch_pos')
    peter_pos = z3.Int('peter_pos')
    solver.add(z3.Or([z3.And(style_vars[i] == 2, ranch_pos == i) for i in range(4)]))
    solver.add(z3.Or([z3.And(name_vars[i] == 3, peter_pos == i) for i in range(4)]))
    solver.add(ranch_pos < peter_pos)
    
    # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house
    # Craftsman is at index 0 in styles list, Arnold is at index 1 in names list
    craftsman_pos = z3.Int('craftsman_pos')
    arnold_pos = z3.Int('arnold_pos')
    solver.add(z3.Or([z3.And(style_vars[i] == 0, craftsman_pos == i) for i in range(4)]))
    solver.add(z3.Or([z3.And(name_vars[i] == 1, arnold_pos == i) for i in range(4)]))
    solver.add(craftsman_pos < arnold_pos)
    
    # Clue 5: The person in a Craftsman-style house is Alice
    # Craftsman is at index 0 in styles list, Alice is at index 2 in names list
    for i in range(4):
        solver.add(z3.Implies(style_vars[i] == 0, name_vars[i] == 2))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract solution
        solution = []
        for house in range(4):
            name_idx = model.evaluate(name_vars[house]).as_long()
            style_idx = model.evaluate(style_vars[house]).as_long()
            
            solution.append({
                "House": str(house + 1),
                "Name": names[name_idx],
                "HouseStyle": styles[style_idx]
            })
        
        # Sort by house number
        solution.sort(key=lambda x: int(x["House"]))
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": [[row["House"], row["Name"], row["HouseStyle"]] for row in solution]
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()