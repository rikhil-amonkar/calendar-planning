from z3 import *
import json

def main():
    s = Solver()

    # Define variables for each house (0-3)
    name = [Int(f"name_{i}") for i in range(4)]
    cigar = [Int(f"cigar_{i}") for i in range(4)]
    sport = [Int(f"sport_{i}") for i in range(4)]
    drink = [Int(f"drink_{i}") for i in range(4)]

    # Add constraints for distinct and bounds
    for var_list in [name, cigar, sport, drink]:
        s.add(Distinct(var_list))
        for var in var_list:
            s.add(And(0 <= var, var <= 3))

    # Add puzzle constraints
    # Clue 1: Peter is in the fourth house (index 3)
    s.add(name[3] == 1)  # Peter is 1

    # Clue 2 and 8: The tea drinker (drink=3) is in the third house (index 2)
    s.add(drink[2] == 3)  # Tea is 3

    # Clue 8: The basketball lover is in the third house (index 2)
    s.add(sport[2] == 1)  # Basketball is 1

    # Clue 4: The basketball lover is Eric (index 2, name=3)
    s.add(name[2] == 3)  # Eric is 3

    # Clue 6: Two houses between water drinker and Peter (index 3)
    s.add(drink[0] == 1)  # Water is 1

    # Clue 3: Arnold (name=2) smokes Blue Master (cigar=2)
    for i in range(4):
        s.add(Implies(name[i] == 2, cigar[i] == 2))  # Arnold is 2, Blue Master is 2

    # Clue 5: The tennis lover (sport=3) smokes Blue Master (cigar=2)
    for i in range(4):
        s.add(Implies(sport[i] == 3, cigar[i] == 2))  # Tennis is 3

    # Clue 7: Arnold (name=2) drinks coffee (drink=0)
    for i in range(4):
        s.add(Implies(name[i] == 2, drink[i] == 0))  # Coffee is 0

    # Clue 9: Prince smoker (cigar=0) loves soccer (sport=2)
    for i in range(4):
        s.add(Implies(cigar[i] == 0, sport[i] == 2))  # Prince is 0, Soccer is 2

    # Clue 10: Peter (index 3) smokes Pall Mall (cigar=3)
    s.add(cigar[3] == 3)  # Pall Mall is 3

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()

        # Mapping from integer codes to strings
        names_list = ["Alice", "Peter", "Arnold", "Eric"]
        cigars_list = ["prince", "dunhill", "blue master", "pall mall"]
        sports_list = ["swimming", "basketball", "soccer", "tennis"]
        drinks_list = ["coffee", "water", "milk", "tea"]

        rows = []
        for i in range(4):
            house_num = i + 1
            n = model[name[i]].as_long()
            c = model[cigar[i]].as_long()
            sp = model[sport[i]].as_long()
            d = model[drink[i]].as_long()
            row = [
                str(house_num),
                names_list[n],
                cigars_list[c],
                sports_list[sp],
                drinks_list[d]
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()