import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define enums for attributes
    NameSort, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
    SportSort, (basketball, soccer) = EnumSort('Sport', ['basketball', 'soccer'])
    HobbySort, (photography, gardening) = EnumSort('Hobby', ['photography', 'gardening'])
    
    # Create variables for each house
    houses = [0, 1]  # 0-indexed for houses 1 and 2
    names = [Const(f'name_{i}', NameSort) for i in houses]
    sports = [Const(f'sport_{i}', SportSort) for i in houses]
    hobbies = [Const(f'hobby_{i}', HobbySort) for i in houses]
    
    # Add uniqueness constraints
    solver.add(Distinct(names))
    solver.add(Distinct(sports))
    solver.add(Distinct(hobbies))
    
    # Clue 1: The person who enjoys gardening is Arnold.
    for i in houses:
        solver.add(Implies(hobbies[i] == gardening, names[i] == Arnold))
    
    # Clue 2: The photography enthusiast is not in the first house.
    solver.add(hobbies[0] != photography)
    
    # Clue 3: The person who loves soccer is not in the first house.
    solver.add(sports[0] != soccer)
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare results
        rows = []
        for i in houses:
            name_val = model.eval(names[i])
            sport_val = model.eval(sports[i])
            hobby_val = model.eval(hobbies[i])
            
            # Convert Z3 values to strings
            name_str = str(name_val)
            sport_str = str(sport_val)
            hobby_str = str(hobby_val)
            
            rows.append([str(i+1), name_str, sport_str, hobby_str])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()