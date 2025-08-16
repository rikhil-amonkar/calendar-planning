#!/usr/bin/env python3
import itertools
import json

def solve():
    names = ["Alice", "Peter", "Arnold", "Eric"]
    cigars = ["prince", "dunhill", "blue master", "pall mall"]
    sports = ["swimming", "basketball", "soccer", "tennis"]
    drinks = ["coffee", "water", "milk", "tea"]
    
    # Houses are indexed 0..3 corresponding to house numbers 1..4
    for perm_names in itertools.permutations(names):
        # Clue 1: Peter is in the fourth house.
        if perm_names[3] != "Peter":
            continue

        for perm_cigars in itertools.permutations(cigars):
            # Clue 3: Arnold is the person who smokes Blue Master.
            idx_arnold = perm_names.index("Arnold")
            if perm_cigars[idx_arnold] != "blue master":
                continue
            # Clue 10: Peter is the person partial to Pall Mall.
            idx_peter = perm_names.index("Peter")
            if perm_cigars[idx_peter] != "pall mall":
                continue

            for perm_sports in itertools.permutations(sports):
                # Clue 8: The person who loves basketball is in the third house.
                if perm_sports[2] != "basketball":
                    continue
                # Clue 4: The person who loves basketball is Eric.
                idx_eric = perm_names.index("Eric")
                if perm_sports[idx_eric] != "basketball":
                    continue
                # Clue 5: The person who loves tennis is the person who smokes Blue Master.
                if perm_sports[idx_arnold] != "tennis":
                    continue
                # Clue 9: The Prince smoker is the person who loves soccer.
                idx_prince = perm_cigars.index("prince")
                if perm_sports[idx_prince] != "soccer":
                    continue

                for perm_drinks in itertools.permutations(drinks):
                    # Clue 2: The tea drinker is the person who loves basketball.
                    if "tea" in perm_drinks:
                        idx_tea = perm_drinks.index("tea")
                        if perm_sports[idx_tea] != "basketball":
                            continue
                    # Clue 7: The coffee drinker is Arnold.
                    if perm_drinks[idx_arnold] != "coffee":
                        continue
                    # Clue 6: There are two houses between the one who only drinks water and Peter.
                    idx_water = perm_drinks.index("water")
                    if abs(idx_peter - idx_water) != 3:
                        continue

                    # If all constraints are met, build the solution.
                    solution = []
                    for i in range(4):
                        solution.append([str(i+1), perm_names[i], perm_cigars[i], perm_sports[i], perm_drinks[i]])
                    return solution
    return None

def main():
    solution_rows = solve()
    result = {
        "solution": {
            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
            "rows": solution_rows
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()