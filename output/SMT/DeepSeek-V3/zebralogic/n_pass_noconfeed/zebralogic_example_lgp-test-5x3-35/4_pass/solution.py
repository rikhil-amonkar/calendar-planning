import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3, 4, 5]
    
    # Define attributes
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
    heights = ['average', 'very short', 'short', 'very tall', 'tall']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    mother_vars = [z3.Int(f'mother_{h}') for h in houses]
    height_vars = [z3.Int(f'height_{h}') for h in houses]
    
    # Constraint: all attributes are within valid range (0-4)
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < 5))
        solver.add(z3.And(mother_vars[h-1] >= 0, mother_vars[h-1] < 5))
        solver.add(z3.And(height_vars[h-1] >= 0, height_vars[h-1] < 5))
    
    # Constraint: all attributes are distinct within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(mother_vars))
    solver.add(z3.Distinct(height_vars))
    
    # Helper function to get index of a value in a list
    def idx(lst, val):
        return lst.index(val)
    
    # Clue 1: Alice is The person whose mother's name is Aniya.
    alice_name_idx = idx(names, 'Alice')
    aniya_mother_idx = idx(mothers, 'Aniya')
    for h in houses:
        solver.add(z3.Implies(name_vars[h-1] == alice_name_idx, 
                            mother_vars[h-1] == aniya_mother_idx))
    
    # Clue 2: The person who has an average height is somewhere to the left of The person whose mother's name is Penny.
    avg_height_idx = idx(heights, 'average')
    penny_mother_idx = idx(mothers, 'Penny')
    
    # Create constraints for "somewhere to the left"
    avg_height_house = z3.Int('avg_height_house')
    penny_mother_house = z3.Int('penny_mother_house')
    
    # Link the house variables to the actual positions
    for h in houses:
        solver.add(z3.Implies(height_vars[h-1] == avg_height_idx, avg_height_house == h))
        solver.add(z3.Implies(mother_vars[h-1] == penny_mother_idx, penny_mother_house == h))
    
    solver.add(avg_height_house < penny_mother_house)
    
    # Clue 3: The person whose mother's name is Janelle is Bob.
    janelle_mother_idx = idx(mothers, 'Janelle')
    bob_name_idx = idx(names, 'Bob')
    for h in houses:
        solver.add(z3.Implies(mother_vars[h-1] == janelle_mother_idx, 
                            name_vars[h-1] == bob_name_idx))
    
    # Clue 4: Peter is not in the second house.
    peter_name_idx = idx(names, 'Peter')
    solver.add(name_vars[1] != peter_name_idx)  # house 2 is index 1
    
    # Clue 5: The person who is short is directly left of Arnold.
    short_height_idx = idx(heights, 'short')
    arnold_name_idx = idx(names, 'Arnold')
    
    # Arnold must be in house 2-5, and short person in house immediately before
    # Use a more direct approach for "directly left"
    arnold_house = z3.Int('arnold_house')
    short_house = z3.Int('short_house')
    
    # Link Arnold to his house
    for h in houses:
        solver.add(z3.Implies(name_vars[h-1] == arnold_name_idx, arnold_house == h))
    
    # Link short height to its house
    for h in houses:
        solver.add(z3.Implies(height_vars[h-1] == short_height_idx, short_house == h))
    
    # Directly left constraint
    solver.add(short_house + 1 == arnold_house)
    
    # Clue 6: The person who is very tall is Arnold.
    very_tall_height_idx = idx(heights, 'very tall')
    for h in houses:
        solver.add(z3.Implies(height_vars[h-1] == very_tall_height_idx, 
                            name_vars[h-1] == arnold_name_idx))
    
    # Clue 7: Bob is directly left of the person who has an average height.
    bob_house = z3.Int('bob_house')
    avg_height_house2 = z3.Int('avg_height_house2')
    
    # Link Bob to his house
    for h in houses:
        solver.add(z3.Implies(name_vars[h-1] == bob_name_idx, bob_house == h))
    
    # Link average height to its house
    for h in houses:
        solver.add(z3.Implies(height_vars[h-1] == avg_height_idx, avg_height_house2 == h))
    
    # Directly left constraint
    solver.add(bob_house + 1 == avg_height_house2)
    
    # Clue 8: Eric is not in the fifth house.
    eric_name_idx = idx(names, 'Eric')
    solver.add(name_vars[4] != eric_name_idx)  # house 5 is index 4
    
    # Clue 9: The person who is very tall is somewhere to the right of The person whose mother's name is Holly.
    holly_mother_idx = idx(mothers, 'Holly')
    
    # Create constraints for "somewhere to the right"
    very_tall_house = z3.Int('very_tall_house')
    holly_mother_house = z3.Int('holly_mother_house')
    
    # Link the house variables to the actual positions
    for h in houses:
        solver.add(z3.Implies(height_vars[h-1] == very_tall_height_idx, very_tall_house == h))
        solver.add(z3.Implies(mother_vars[h-1] == holly_mother_idx, holly_mother_house == h))
    
    solver.add(very_tall_house > holly_mother_house)
    
    # Clue 10: Eric is The person whose mother's name is Kailyn.
    kailyn_mother_idx = idx(mothers, 'Kailyn')
    for h in houses:
        solver.add(z3.Implies(name_vars[h-1] == eric_name_idx, 
                            mother_vars[h-1] == kailyn_mother_idx))
    
    # Clue 11: The person who is very short is in the fifth house.
    very_short_height_idx = idx(heights, 'very short')
    solver.add(height_vars[4] == very_short_height_idx)  # house 5 is index 4
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Mother", "Height"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for h in houses:
            name_idx = model.evaluate(name_vars[h-1]).as_long()
            mother_idx = model.evaluate(mother_vars[h-1]).as_long()
            height_idx = model.evaluate(height_vars[h-1]).as_long()
            
            row = [
                str(h),
                names[name_idx],
                mothers[mother_idx],
                heights[height_idx]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()