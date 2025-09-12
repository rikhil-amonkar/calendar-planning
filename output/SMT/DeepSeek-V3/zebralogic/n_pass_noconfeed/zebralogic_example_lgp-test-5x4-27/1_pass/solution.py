import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define the attributes
    names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
    months = ['april', 'feb', 'mar', 'jan', 'sept']
    cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
    drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in range(5)]
    month_vars = [Int(f'month_{i}') for i in range(5)]
    cigar_vars = [Int(f'cigar_{i}') for i in range(5)]
    drink_vars = [Int(f'drink_{i}') for i in range(5)]
    
    # Constrain all variables to be within 0-4 (indexes)
    for i in range(5):
        s.add(And(name_vars[i] >= 0, name_vars[i] < 5))
        s.add(And(month_vars[i] >= 0, month_vars[i] < 5))
        s.add(And(cigar_vars[i] >= 0, cigar_vars[i] < 5))
        s.add(And(drink_vars[i] >= 0, drink_vars[i] < 5))
    
    # All attributes must have distinct values per house
    s.add(Distinct(name_vars))
    s.add(Distinct(month_vars))
    s.add(Distinct(cigar_vars))
    s.add(Distinct(drink_vars))
    
    # Clue 1: The root beer lover is Eric.
    # Eric drinks root beer
    eric_idx = names.index('Eric')
    root_beer_idx = drinks.index('root beer')
    s.add(Exists([i], And(i >= 0, i < 5, name_vars[i] == eric_idx, drink_vars[i] == root_beer_idx)))
    
    # Clue 2: The person partial to Pall Mall is in the third house.
    pall_mall_idx = cigars.index('pall mall')
    s.add(cigar_vars[2] == pall_mall_idx)
    
    # Clue 3: The person whose birthday is in April is Bob.
    april_idx = months.index('april')
    bob_idx = names.index('Bob')
    s.add(Exists([i], And(i >= 0, i < 5, month_vars[i] == april_idx, name_vars[i] == bob_idx)))
    
    # Clue 4: The Dunhill smoker is the person whose birthday is in March.
    dunhill_idx = cigars.index('dunhill')
    mar_idx = months.index('mar')
    s.add(Exists([i], And(i >= 0, i < 5, cigar_vars[i] == dunhill_idx, month_vars[i] == mar_idx)))
    
    # Clue 5: Peter is somewhere to the right of the root beer lover.
    peter_idx = names.index('Peter')
    # Find house where drink is root beer, then Peter must be in a higher numbered house
    s.add(ForAll([i], Implies(And(i >= 0, i < 5, drink_vars[i] == root_beer_idx), 
                             Exists([j], And(j > i, j < 5, name_vars[j] == peter_idx))))
    
    # Clue 6: There is one house between the person whose birthday is in January and Peter.
    jan_idx = months.index('jan')
    # |house(jan) - house(peter)| = 2
    s.add(Exists([i, j], And(i >= 0, i < 5, j >= 0, j < 5, month_vars[i] == jan_idx, 
                            name_vars[j] == peter_idx, Or(i == j + 2, j == i + 2))))
    
    # Clue 7: The person who smokes many unique blends is the person whose birthday is in February.
    blends_idx = cigars.index('blends')
    feb_idx = months.index('feb')
    s.add(Exists([i], And(i >= 0, i < 5, cigar_vars[i] == blends_idx, month_vars[i] == feb_idx)))
    
    # Clue 8: The person whose birthday is in February is in the second house.
    s.add(month_vars[1] == feb_idx)
    
    # Clue 9: Arnold is directly left of Peter.
    arnold_idx = names.index('Arnold')
    # Arnold in house i, Peter in house i+1
    s.add(Exists([i], And(i >= 0, i < 4, name_vars[i] == arnold_idx, name_vars[i+1] == peter_idx)))
    
    # Clue 10: The person who likes milk is not in the fifth house.
    milk_idx = drinks.index('milk')
    s.add(drink_vars[4] != milk_idx)
    
    # Clue 11: The person who smokes Blue Master is the coffee drinker.
    blue_master_idx = cigars.index('blue master')
    coffee_idx = drinks.index('coffee')
    s.add(Exists([i], And(i >= 0, i < 5, cigar_vars[i] == blue_master_idx, drink_vars[i] == coffee_idx)))
    
    # Clue 12: There is one house between the tea drinker and the coffee drinker.
    tea_idx = drinks.index('tea')
    # |house(tea) - house(coffee)| = 2
    s.add(Exists([i, j], And(i >= 0, i < 5, j >= 0, j < 5, drink_vars[i] == tea_idx, 
                            drink_vars[j] == coffee_idx, Or(i == j + 2, j == i + 2))))
    
    # Clue 13: Eric is in the third house.
    s.add(name_vars[2] == eric_idx)
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in range(5):
            name_val = model.eval(name_vars[house]).as_long()
            month_val = model.eval(month_vars[house]).as_long()
            cigar_val = model.eval(cigar_vars[house]).as_long()
            drink_val = model.eval(drink_vars[house]).as_long()
            
            row = [
                str(house + 1),
                names[name_val],
                months[month_val],
                cigars[cigar_val],
                drinks[drink_val]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()