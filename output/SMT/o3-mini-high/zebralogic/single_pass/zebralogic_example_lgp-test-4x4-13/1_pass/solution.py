from z3 import *
import json

def main():
    s = Solver()
    houses = 4

    # For each house (indexed 0..3 corresponding to House 1 to 4),
    # we create variables for Name, Cigar, Sport, Drink.
    names   = [Int(f"name_{i}") for i in range(houses)]
    cigars  = [Int(f"cigar_{i}") for i in range(houses)]
    sports  = [Int(f"sport_{i}") for i in range(houses)]
    drinks  = [Int(f"drink_{i}") for i in range(houses)]

    # We use integer values for each attribute with the following mappings:
    # Name:     0: Alice, 1: Peter,   2: Arnold, 3: Eric
    # Cigar:    0: prince, 1: dunhill, 2: blue master, 3: pall mall
    # Sport:    0: swimming, 1: basketball, 2: soccer, 3: tennis
    # Drink:    0: coffee, 1: water, 2: milk, 3: tea

    # Domain constraints: each variable must be in 0..3
    for i in range(houses):
        s.add(And(names[i]  >= 0, names[i]  <= 3))
        s.add(And(cigars[i] >= 0, cigars[i] <= 3))
        s.add(And(sports[i] >= 0, sports[i] <= 3))
        s.add(And(drinks[i] >= 0, drinks[i] <= 3))
    
    # Each house has a distinct attribute value per category.
    s.add(Distinct(names))
    s.add(Distinct(cigars))
    s.add(Distinct(sports))
    s.add(Distinct(drinks))
    
    # --- Clue constraints ---
    # Clue 1: "Peter is in the fourth house."
    # House 4 is index 3 and Peter is represented by 1.
    s.add(names[3] == 1)

    # Clue 2: "The tea drinker is the person who loves basketball."
    # tea is 3 and basketball is 1.
    for i in range(houses):
        s.add(Or(And(drinks[i] == 3, sports[i] == 1),
                 And(drinks[i] != 3, sports[i] != 1)))
    
    # Clue 3: "Arnold is the person who smokes Blue Master."
    # Arnold is 2 and blue master is 2.
    for i in range(houses):
        s.add((names[i] == 2) == (cigars[i] == 2))
    
    # Clue 4: "The person who loves basketball is Eric."
    # Basketball is 1 and Eric is 3.
    for i in range(houses):
        s.add((sports[i] == 1) == (names[i] == 3))
    
    # Clue 5: "The person who loves tennis is the person who smokes Blue Master."
    # Tennis is 3 and blue master is 2.
    for i in range(houses):
        s.add((sports[i] == 3) == (cigars[i] == 2))
    
    # Clue 6: "There are two houses between the one who only drinks water and Peter."
    # With only 4 houses and Peter in the fourth house (index 3),
    # the only possibility is that water (represented by 1) is drunk in house 1 (index 0).
    s.add(drinks[0] == 1)
    
    # Clue 7: "The coffee drinker is Arnold."
    # Coffee is 0 and Arnold is 2.
    for i in range(houses):
        s.add((drinks[i] == 0) == (names[i] == 2))
    
    # Clue 8: "The person who loves basketball is in the third house."
    # House 3 is index 2.
    s.add(sports[2] == 1)
    
    # Clue 9: "The Prince smoker is the person who loves soccer."
    # Prince is 0 and soccer is 2.
    for i in range(houses):
        s.add((cigars[i] == 0) == (sports[i] == 2))
    
    # Clue 10: "Peter is the person partial to Pall Mall."
    # Peter is 1 and pall mall is 3.
    for i in range(houses):
        s.add((names[i] == 1) == (cigars[i] == 3))
    
    # --- Solve the puzzle ---
    if s.check() == sat:
        m = s.model()
        # Maps for converting integer values back to string values.
        name_map  = {0: "Alice", 1: "Peter", 2: "Arnold", 3: "Eric"}
        cigar_map = {0: "prince", 1: "dunhill", 2: "blue master", 3: "pall mall"}
        sport_map = {0: "swimming", 1: "basketball", 2: "soccer", 3: "tennis"}
        drink_map = {0: "coffee", 1: "water", 2: "milk", 3: "tea"}
        
        solution_rows = []
        for i in range(houses):
            # Houses are numbered 1 to 4 (i+1)
            house_num = str(i + 1)
            name_val  = name_map[m.evaluate(names[i]).as_long()]
            cigar_val = cigar_map[m.evaluate(cigars[i]).as_long()]
            sport_val = sport_map[m.evaluate(sports[i]).as_long()]
            drink_val = drink_map[m.evaluate(drinks[i]).as_long()]
            solution_rows.append([house_num, name_val, cigar_val, sport_val, drink_val])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()