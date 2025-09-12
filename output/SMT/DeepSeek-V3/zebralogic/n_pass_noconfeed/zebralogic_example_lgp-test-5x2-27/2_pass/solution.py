from z3 import *
import json

def main():
    solver = Solver()
    
    houses = [1, 2, 3, 4, 5]
    names = ['Peter', 'Alice', 'Bob', 'Eric', 'Arnold']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']
    
    name_vars = [Int(f'name_{i}') for i in houses]
    height_vars = [Int(f'height_{i}') for i in houses]
    
    # Constrain variables to valid indices
    for i in range(5):
        solver.add(name_vars[i] >= 0, name_vars[i] < 5)
        solver.add(height_vars[i] >= 0, height_vars[i] < 5)
    
    solver.add(Distinct(name_vars))
    solver.add(Distinct(height_vars))
    
    # Get indices for easier reference
    peter_idx = names.index('Peter')
    alice_idx = names.index('Alice')
    bob_idx = names.index('Bob')
    eric_idx = names.index('Eric')
    arnold_idx = names.index('Arnold')
    
    very_tall_idx = heights.index('very tall')
    average_idx = heights.index('average')
    tall_idx = heights.index('tall')
    very_short_idx = heights.index('very short')
    short_idx = heights.index('short')
    
    # Clue 1: The person who is short is in the second house.
    solver.add(height_vars[1] == short_idx)  # House 2 is index 1
    
    # Clue 2: Peter is directly left of Bob.
    for i in range(4):
        solver.add(Implies(name_vars[i] == peter_idx, name_vars[i+1] == bob_idx))
    
    # Clue 3: Eric is somewhere to the left of Peter.
    # This means Eric's house number < Peter's house number
    peter_house = Int('peter_house')
    eric_house = Int('eric_house')
    solver.add(peter_house >= 0, peter_house < 5)
    solver.add(eric_house >= 0, eric_house < 5)
    
    for i in range(5):
        solver.add(Implies(name_vars[i] == peter_idx, peter_house == i))
        solver.add(Implies(name_vars[i] == eric_idx, eric_house == i))
    
    solver.add(eric_house < peter_house)
    
    # Clue 4: The person who is very tall is directly left of Peter.
    for i in range(4):
        solver.add(Implies(name_vars[i+1] == peter_idx, height_vars[i] == very_tall_idx))
    
    # Clue 5: Alice is directly left of the person who has an average height.
    for i in range(4):
        solver.add(Implies(name_vars[i] == alice_idx, height_vars[i+1] == average_idx))
    
    # Clue 6: The person who is short and the person who is very short are next to each other.
    short_pos = Int('short_pos')
    very_short_pos = Int('very_short_pos')
    solver.add(short_pos >= 0, short_pos < 5)
    solver.add(very_short_pos >= 0, very_short_pos < 5)
    
    for i in range(5):
        solver.add(Implies(height_vars[i] == short_idx, short_pos == i))
        solver.add(Implies(height_vars[i] == very_short_idx, very_short_pos == i))
    
    solver.add(Or(short_pos == very_short_pos + 1, short_pos == very_short_pos - 1))
    
    # Clue 7: The person who has an average height is in the fifth house.
    solver.add(height_vars[4] == average_idx)  # House 5 is index 4
    
    if solver.check() == sat:
        model = solver.model()
        
        result = []
        for i in range(5):
            name_val = model.eval(name_vars[i]).as_long()
            height_val = model.eval(height_vars[i]).as_long()
            result.append({
                'house': str(i+1),
                'name': names[name_val],
                'height': heights[height_val]
            })
        
        # Sort by house number
        result.sort(key=lambda x: int(x['house']))
        
        output = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": [[r['house'], r['name'], r['height']] for r in result]
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()