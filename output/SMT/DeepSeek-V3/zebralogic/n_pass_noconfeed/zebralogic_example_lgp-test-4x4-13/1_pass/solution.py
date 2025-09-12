from z3 import *
import json

def main():
    solver = Solver()
    
    # Define the attributes and their possible values
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    cigars = ['prince', 'dunhill', 'blue master', 'pall mall']
    sports = ['swimming', 'basketball', 'soccer', 'tennis']
    drinks = ['coffee', 'water', 'milk', 'tea']
    
    # Create variables for each attribute in each house
    name_vars = [Int(f'name_{i}') for i in range(1, 5)]
    cigar_vars = [Int(f'cigar_{i}') for i in range(1, 5)]
    sport_vars = [Int(f'sport_{i}') for i in range(1, 5)]
    drink_vars = [Int(f'drink_{i}') for i in range(1, 5)]
    
    # Define domains for each variable
    for i in range(4):
        solver.add(And(name_vars[i] >= 0, name_vars[i] < 4))
        solver.add(And(cigar_vars[i] >= 0, cigar_vars[i] < 4))
        solver.add(And(sport_vars[i] >= 0, sport_vars[i] < 4))
        solver.add(And(drink_vars[i] >= 0, drink_vars[i] < 4))
    
    # All attributes must be distinct within their category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(cigar_vars))
    solver.add(Distinct(sport_vars))
    solver.add(Distinct(drink_vars))
    
    # Map integer values to attribute names
    name_map = {0: 'Alice', 1: 'Peter', 2: 'Arnold', 3: 'Eric'}
    cigar_map = {0: 'prince', 1: 'dunhill', 2: 'blue master', 3: 'pall mall'}
    sport_map = {0: 'swimming', 1: 'basketball', 2: 'soccer', 3: 'tennis'}
    drink_map = {0: 'coffee', 1: 'water', 2: 'milk', 3: 'tea'}
    
    # Clue 1: Peter is in the fourth house.
    solver.add(name_vars[3] == 1)  # Peter is index 1
    
    # Clue 2: The tea drinker is the person who loves basketball.
    for i in range(4):
        solver.add(Implies(drink_vars[i] == 3, sport_vars[i] == 1))
    
    # Clue 3: Arnold is the person who smokes Blue Master.
    for i in range(4):
        solver.add(Implies(name_vars[i] == 2, cigar_vars[i] == 2))
    
    # Clue 4: The person who loves basketball is Eric.
    for i in range(4):
        solver.add(Implies(sport_vars[i] == 1, name_vars[i] == 3))
    
    # Clue 5: The person who loves tennis is the person who smokes Blue Master.
    for i in range(4):
        solver.add(Implies(sport_vars[i] == 3, cigar_vars[i] == 2))
    
    # Clue 6: There are two houses between the one who only drinks water and Peter.
    # Peter is in house 4 (index 3), so water drinker must be in house 1 (index 0)
    solver.add(drink_vars[0] == 1)  # water is index 1
    
    # Clue 7: The coffee drinker is Arnold.
    for i in range(4):
        solver.add(Implies(name_vars[i] == 2, drink_vars[i] == 0))
    
    # Clue 8: The person who loves basketball is in the third house.
    solver.add(sport_vars[2] == 1)
    
    # Clue 9: The Prince smoker is the person who loves soccer.
    for i in range(4):
        solver.add(Implies(cigar_vars[i] == 0, sport_vars[i] == 2))
    
    # Clue 10: Peter is the person partial to Pall Mall.
    for i in range(4):
        solver.add(Implies(name_vars[i] == 1, cigar_vars[i] == 3))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare the solution
        rows = []
        for i in range(4):
            name_val = model.evaluate(name_vars[i]).as_long()
            cigar_val = model.evaluate(cigar_vars[i]).as_long()
            sport_val = model.evaluate(sport_vars[i]).as_long()
            drink_val = model.evaluate(drink_vars[i]).as_long()
            
            row = [
                str(i + 1),
                name_map[name_val],
                cigar_map[cigar_val],
                sport_map[sport_val],
                drink_map[drink_val]
            ]
            rows.append(row)
        
        # Create the JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()