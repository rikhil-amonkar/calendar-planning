import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    n_houses = 6
    houses = list(range(1, n_houses+1))
    
    # Define attributes
    names = ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold']
    vacations = ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach']
    
    # Create variables for name and vacation assignments
    name_vars = [Int(f'name_{i}') for i in houses]
    vacation_vars = [Int(f'vacation_{i}') for i in houses]
    
    # Each name variable must be between 0 and 5 (index of names)
    for var in name_vars:
        solver.add(var >= 0, var < len(names))
    
    # Each vacation variable must be between 0 and 5 (index of vacations)
    for var in vacation_vars:
        solver.add(var >= 0, var < len(vacations))
    
    # All names are distinct
    solver.add(Distinct(name_vars))
    
    # All vacations are distinct
    solver.add(Distinct(vacation_vars))
    
    # Clue 2: Eric is somewhere to the right of Alice
    # Find positions of Eric and Alice
    eric_pos = Int('eric_pos')
    alice_pos = Int('alice_pos')
    solver.add(eric_pos >= 1, eric_pos <= n_houses)
    solver.add(alice_pos >= 1, alice_pos <= n_houses)
    
    # Eric is right of Alice
    solver.add(eric_pos > alice_pos)
    
    # Connect positions to name variables
    for i, house in enumerate(houses):
        solver.add(If(name_vars[i] == names.index('Eric'), eric_pos == house, True))
        solver.add(If(name_vars[i] == names.index('Alice'), alice_pos == house, True))
    
    # Clue 3: Eric is in the second house
    solver.add(eric_pos == 2)
    
    # Clue 4: The person who goes on cultural tours is in the third house
    cultural_pos = Int('cultural_pos')
    solver.add(cultural_pos >= 1, cultural_pos <= n_houses)
    solver.add(cultural_pos == 3)
    
    # Connect cultural position to vacation variables
    for i, house in enumerate(houses):
        solver.add(If(vacation_vars[i] == vacations.index('cultural'), cultural_pos == house, True))
    
    # Clue 1: The person who goes on cultural tours is somewhere to the left of the person who loves beach vacations
    beach_pos = Int('beach_pos')
    solver.add(beach_pos >= 1, beach_pos <= n_houses)
    solver.add(cultural_pos < beach_pos)
    
    # Connect beach position to vacation variables
    for i, house in enumerate(houses):
        solver.add(If(vacation_vars[i] == vacations.index('beach'), beach_pos == house, True))
    
    # Clue 5: Bob is directly left of Arnold
    bob_pos = Int('bob_pos')
    arnold_pos = Int('arnold_pos')
    solver.add(bob_pos >= 1, bob_pos <= n_houses)
    solver.add(arnold_pos >= 1, arnold_pos <= n_houses)
    solver.add(arnold_pos == bob_pos + 1)
    
    # Connect positions to name variables
    for i, house in enumerate(houses):
        solver.add(If(name_vars[i] == names.index('Bob'), bob_pos == house, True))
        solver.add(If(name_vars[i] == names.index('Arnold'), arnold_pos == house, True))
    
    # Clue 6: The person who enjoys camping trips is not in the first house
    camping_pos = Int('camping_pos')
    solver.add(camping_pos >= 1, camping_pos <= n_houses)
    solver.add(camping_pos != 1)
    
    # Connect camping position to vacation variables
    for i, house in enumerate(houses):
        solver.add(If(vacation_vars[i] == vacations.index('camping'), camping_pos == house, True))
    
    # Clue 7: The person who goes on cultural tours is Peter
    # Connect cultural vacation to Peter name
    for i, house in enumerate(houses):
        solver.add(If(vacation_vars[i] == vacations.index('cultural'), 
                     name_vars[i] == names.index('Peter'), True))
    
    # Clue 8: The person who likes going on cruises is Bob
    # Connect cruise vacation to Bob name
    for i, house in enumerate(houses):
        solver.add(If(vacation_vars[i] == vacations.index('cruise'), 
                     name_vars[i] == names.index('Bob'), True))
    
    # Clue 9: The person who prefers city breaks is in the fourth house
    city_pos = Int('city_pos')
    solver.add(city_pos >= 1, city_pos <= n_houses)
    solver.add(city_pos == 4)
    
    # Connect city position to vacation variables
    for i, house in enumerate(houses):
        solver.add(If(vacation_vars[i] == vacations.index('city'), city_pos == house, True))
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare solution data
        solution_data = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for i, house_num in enumerate(houses):
            name_idx = model.evaluate(name_vars[i]).as_long()
            vacation_idx = model.evaluate(vacation_vars[i]).as_long()
            
            row = [
                str(house_num),
                names[name_idx],
                vacations[vacation_idx]
            ]
            solution_data["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution_data, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()