#!/usr/bin/env python3
import json
from z3 import Solver, sat, Int, And, Distinct, Implies

def main():
    s = Solver()
    n = 4

    # Create variables for each house (indexed 0 to 3) for each category.
    names = [Int(f"name{i}") for i in range(n)]
    cigars = [Int(f"cigar{i}") for i in range(n)]
    sports = [Int(f"sport{i}") for i in range(n)]
    drinks = [Int(f"drink{i}") for i in range(n)]
    
    # Each variable must be between 0 and 3 (4 possibilities)
    for i in range(n):
        s.add(And(names[i] >= 0, names[i] < n))
        s.add(And(cigars[i] >= 0, cigars[i] < n))
        s.add(And(sports[i] >= 0, sports[i] < n))
        s.add(And(drinks[i] >= 0, drinks[i] < n))
    
    # All houses have distinct attributes for each category.
    s.add(Distinct(names))
    s.add(Distinct(cigars))
    s.add(Distinct(sports))
    s.add(Distinct(drinks))
    
    # Mappings:
    # Names: 0 -> "Alice", 1 -> "Peter", 2 -> "Arnold", 3 -> "Eric"
    # Cigars: 0 -> "prince", 1 -> "dunhill", 2 -> "blue master", 3 -> "pall mall"
    # Sports: 0 -> "swimming", 1 -> "basketball", 2 -> "soccer", 3 -> "tennis"
    # Drinks: 0 -> "coffee", 1 -> "water", 2 -> "milk", 3 -> "tea"
    
    # Clue 1: Peter is in the fourth house.
    s.add(names[3] == 1)
    
    # Clue 2: The tea drinker is the person who loves basketball.
    for i in range(n):
        s.add(And(Implies(drinks[i] == 3, sports[i] == 1),
                  Implies(sports[i] == 1, drinks[i] == 3)))
    
    # Clue 3: Arnold is the person who smokes Blue Master.
    for i in range(n):
        s.add(And(Implies(names[i] == 2, cigars[i] == 2),
                  Implies(cigars[i] == 2, names[i] == 2)))
    
    # Clue 4: The person who loves basketball is Eric.
    for i in range(n):
        s.add(And(Implies(sports[i] == 1, names[i] == 3),
                  Implies(names[i] == 3, sports[i] == 1)))
    
    # Clue 5: The person who loves tennis is the person who smokes Blue Master.
    for i in range(n):
        s.add(And(Implies(sports[i] == 3, cigars[i] == 2),
                  Implies(cigars[i] == 2, sports[i] == 3)))
    
    # Clue 6: There are two houses between the one who drinks water and Peter.
    # Since Peter is in house 4 (index 3), the water drinker must be in house 1 (index 0).
    s.add(drinks[0] == 1)
    
    # Clue 7: The coffee drinker is Arnold.
    for i in range(n):
        s.add(And(Implies(names[i] == 2, drinks[i] == 0),
                  Implies(drinks[i] == 0, names[i] == 2)))
    
    # Clue 8: The person who loves basketball is in the third house.
    s.add(sports[2] == 1)
    
    # Clue 9: The Prince smoker is the person who loves soccer.
    for i in range(n):
        s.add(And(Implies(cigars[i] == 0, sports[i] == 2),
                  Implies(sports[i] == 2, cigars[i] == 0)))
    
    # Clue 10: Peter is the person partial to Pall Mall.
    for i in range(n):
        s.add(And(Implies(names[i] == 1, cigars[i] == 3),
                  Implies(cigars[i] == 3, names[i] == 1)))
    
    if s.check() == sat:
        m = s.model()
        name_map = {0: "Alice", 1: "Peter", 2: "Arnold", 3: "Eric"}
        cigar_map = {0: "prince", 1: "dunhill", 2: "blue master", 3: "pall mall"}
        sport_map = {0: "swimming", 1: "basketball", 2: "soccer", 3: "tennis"}
        drink_map = {0: "coffee", 1: "water", 2: "milk", 3: "tea"}
        
        rows = []
        for i in range(n):
            row = [
                str(i+1),
                name_map[m.evaluate(names[i]).as_long()],
                cigar_map[m.evaluate(cigars[i]).as_long()],
                sport_map[m.evaluate(sports[i]).as_long()],
                drink_map[m.evaluate(drinks[i]).as_long()]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == '__main__':
    main()