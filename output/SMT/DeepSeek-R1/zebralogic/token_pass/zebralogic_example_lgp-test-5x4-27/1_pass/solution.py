import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define attributes and their integer mappings
    names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
    name_to_int = {name: i for i, name in enumerate(names)}
    
    birthdays = ['april', 'feb', 'mar', 'jan', 'sept']
    bday_to_int = {bday: i for i, bday in enumerate(birthdays)}
    
    cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
    cigar_to_int = {cigar: i for i, cigar in enumerate(cigars)}
    
    drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']
    drink_to_int = {drink: i for i, drink in enumerate(drinks)}
    
    # Create Z3 variables for each house (0-indexed: house0 = house1, etc.)
    name_vars = [Int(f'name_{i}') for i in range(5)]
    bday_vars = [Int(f'bday_{i}') for i in range(5)]
    cigar_vars = [Int(f'cigar_{i}') for i in range(5)]
    drink_vars = [Int(f'drink_{i}') for i in range(5)]
    
    # Constraint: All attributes are between 0 and 4
    for i in range(5):
        solver.add(And(name_vars[i] >= 0, name_vars[i] < 5))
        solver.add(And(bday_vars[i] >= 0, bday_vars[i] < 5))
        solver.add(And(cigar_vars[i] >= 0, cigar_vars[i] < 5))
        solver.add(And(drink_vars[i] >= 0, drink_vars[i] < 5))
    
    # Constraint: All attributes are distinct
    solver.add(Distinct(name_vars))
    solver.add(Distinct(bday_vars))
    solver.add(Distinct(cigar_vars))
    solver.add(Distinct(drink_vars))
    
    # Clue 13: Eric is in the third house (index 2)
    solver.add(name_vars[2] == name_to_int['Eric'])
    
    # Clue 1: The root beer lover is Eric -> Eric drinks root beer
    solver.add(drink_vars[2] == drink_to_int['root beer'])
    
    # Clue 2: Pall Mall smoker in third house
    solver.add(cigar_vars[2] == cigar_to_int['pall mall'])
    
    # Clue 3: April birthday is Bob
    solver.add(Exists([i], And(Implies(bday_vars[i] == bday_to_int['april'], name_vars[i] == name_to_int['Bob']), i >= 0, i < 5)))
    
    # Clue 4: Dunhill smoker has March birthday
    for i in range(5):
        solver.add(Implies(cigar_vars[i] == cigar_to_int['dunhill'], bday_vars[i] == bday_to_int['mar']))
    
    # Clue 5: Peter is right of root beer lover (Eric in house 3)
    peter_idx = Int('peter_idx')
    solver.add(Exists([i], And(name_vars[i] == name_to_int['Peter'], i > 2)))
    
    # Clue 6: One house between January birthday and Peter
    jan_idx = Int('jan_idx')
    peter_idx = Int('peter_idx2')
    solver.add(Exists([i, j], And(
        bday_vars[i] == bday_to_int['jan'],
        name_vars[j] == name_to_int['Peter'],
        Or(And(j == i+2), And(j == i-2))
    )))
    
    # Clue 7: Blends smoker has February birthday
    for i in range(5):
        solver.add(Implies(cigar_vars[i] == cigar_to_int['blends'], bday_vars[i] == bday_to_int['feb']))
    
    # Clue 8: February birthday in second house (index 1)
    solver.add(bday_vars[1] == bday_to_int['feb'])
    
    # Clue 9: Arnold directly left of Peter
    for i in range(1, 5):
        solver.add(Implies(name_vars[i] == name_to_int['Peter'], name_vars[i-1] == name_to_int['Arnold']))
    
    # Clue 10: Milk not in fifth house (index 4)
    solver.add(drink_vars[4] != drink_to_int['milk'])
    
    # Clue 11: Blue Master smoker drinks coffee
    for i in range(5):
        solver.add(Implies(cigar_vars[i] == cigar_to_int['blue master'], drink_vars[i] == drink_to_int['coffee']))
    
    # Clue 12: One house between tea and coffee drinker
    tea_idx = Int('tea_idx')
    coffee_idx = Int('coffee_idx')
    solver.add(Exists([i, j], And(
        drink_vars[i] == drink_to_int['tea'],
        drink_vars[j] == drink_to_int['coffee'],
        Or(And(j == i+2), And(j == i-2))
    )))
    
    # Check and get solution
    if solver.check() == sat:
        model = solver.model()
        
        # Build results
        rows = []
        for i in range(5):
            name_val = model.eval(name_vars[i]).as_long()
            bday_val = model.eval(bday_vars[i]).as_long()
            cigar_val = model.eval(cigar_vars[i]).as_long()
            drink_val = model.eval(drink_vars[i]).as_long()
            
            row = [
                str(i+1),
                names[name_val],
                birthdays[bday_val],
                cigars[cigar_val],
                drinks[drink_val]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()