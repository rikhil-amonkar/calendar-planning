import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define attributes
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    styles = ['victorian', 'ranch', 'colonial', 'craftsman']
    
    # Create variables for each house (0-indexed: house0 = house1, house1 = house2, etc.)
    name_vars = [Int(f'name_{i}') for i in range(4)]
    style_vars = [Int(f'style_{i}') for i in range(4)]
    
    # Add domain constraints
    for i in range(4):
        s.add(And(name_vars[i] >= 0, name_vars[i] <= 3))
        s.add(And(style_vars[i] >= 0, style_vars[i] <= 3))
    
    # All names and styles are distinct
    s.add(Distinct(name_vars))
    s.add(Distinct(style_vars))
    
    # Clue 3: Eric is in the third house (index 2)
    s.add(name_vars[2] == 2)  # Eric is index 2 in names
    
    # Clue 4: Arnold is in the fourth house (index 3)
    s.add(name_vars[3] == 0)  # Arnold is index 0 in names
    
    # Clue 1: Eric is in Craftsman house (style index 3)
    s.add(style_vars[2] == 3)  # Craftsman is index 3 in styles
    
    # Clue 2: Ranch (style index 1) is directly left of Victorian (style index 0)
    s.add(Or(
        And(style_vars[0] == 1, style_vars[1] == 0),
        And(style_vars[1] == 1, style_vars[2] == 0),
        And(style_vars[2] == 1, style_vars[3] == 0)
    ))
    
    # Clue 5: Victorian house (style index 0) is Alice (name index 3)
    for i in range(4):
        s.add(Implies(style_vars[i] == 0, name_vars[i] == 3))
    
    # Check solution
    if s.check() == sat:
        m = s.model()
        result = []
        for i in range(4):
            name_idx = m.evaluate(name_vars[i]).as_long()
            style_idx = m.evaluate(style_vars[i]).as_long()
            result.append({
                'house': str(i+1),
                'name': names[name_idx],
                'style': styles[style_idx]
            })
        
        # Format output JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": [[r['house'], r['name'], r['style']] for r in result]
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()