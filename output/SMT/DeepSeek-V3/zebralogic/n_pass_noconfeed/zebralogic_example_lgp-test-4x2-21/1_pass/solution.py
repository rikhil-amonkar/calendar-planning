import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Eric', 'Arnold', 'Alice', 'Peter']
    styles = ['craftsman', 'colonial', 'ranch', 'victorian']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    style_vars = [z3.Int(f'style_{h}') for h in houses]
    
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
    # Alice is at index 2 in names list
    solver.add(name_vars[1] == 2)
    
    # Clue 2: The person residing in a Victorian house is directly left of Peter
    # Victorian is at index 3 in styles list, Peter is at index 3 in names list
    for i in range(3):  # Check houses 1-3 (since Victorian must be left of Peter)
        solver.add(z3.Implies(style_vars[i] == 3, name_vars[i+1] == 3))
    
    # Clue 3: Peter is somewhere to the right of the person in a ranch-style home
    # Ranch is at index 2 in styles list, Peter is at index 3 in names list
    for i in range(4):
        for j in range(i+1, 4):
            solver.add(z3.Implies(style_vars[i] == 2, name_vars[j] == 3))
    
    # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house
    # Craftsman is at index 0 in styles list, Arnold is at index 1 in names list
    for i in range(4):
        for j in range(i+1, 4):
            solver.add(z3.Implies(style_vars[i] == 0, name_vars[j] == 1))
    
    # Clue 5: The person in a Craftsman-style house is Alice
    # Craftsman is at index 0 in styles list, Alice is at index 2 in names list
    for i in range(4):
        solver.add(z3.Implies(style_vars[i] == 0, name_vars[i] == 2))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract solution
        solution = []
        for house in houses:
            name_idx = model.evaluate(name_vars[house-1]).as_long()
            style_idx = model.evaluate(style_vars[house-1]).as_long()
            
            solution.append({
                "House": str(house),
                "Name": names[name_idx],
                "HouseStyle": styles[style_idx]
            })
        
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