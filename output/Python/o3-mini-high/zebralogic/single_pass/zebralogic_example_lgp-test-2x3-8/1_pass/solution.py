#!/usr/bin/env python3
import json
import itertools

def solve_puzzle():
    names = ["Arnold", "Eric"]
    birthdays = ["april", "sept"]
    mothers = ["Aniya", "Holly"]
    
    houses_index = [1, 2]  # house numbers: 1 (left), 2 (right)
    
    # Try all permutations of attributes for the houses
    for name_perm in itertools.permutations(names):
        for birthday_perm in itertools.permutations(birthdays):
            for mother_perm in itertools.permutations(mothers):
                # Build houses as dictionaries: index 0 -> house 1, index 1 -> house 2
                house1 = {"House": "1", "Name": name_perm[0], "Birthday": birthday_perm[0], "Mother": mother_perm[0]}
                house2 = {"House": "2", "Name": name_perm[1], "Birthday": birthday_perm[1], "Mother": mother_perm[1]}
                houses = [house1, house2]
                
                # Constraint 2: The person whose birthday is in April is in the first house.
                if house1["Birthday"] != "april":
                    continue
                
                # Constraint 1: Eric is somewhere to the left of the person whose mother's name is Holly.
                # Find the positions of Eric and the house with Holly as the mother.
                pos_eric = None
                pos_holly = None
                for idx, house in enumerate(houses):
                    if house["Name"] == "Eric":
                        pos_eric = idx
                    if house["Mother"] == "Holly":
                        pos_holly = idx
                
                # If either was not found or if Eric is not to the left of Holly, then skip.
                if pos_eric is None or pos_holly is None or pos_eric >= pos_holly:
                    continue
                
                # Found valid solution; return it.
                return houses
    return None

def main():
    solution_houses = solve_puzzle()
    if solution_houses is None:
        result = {"solution": "No solution found"}
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother"],
                "rows": [
                    [solution_houses[0]["House"], solution_houses[0]["Name"], solution_houses[0]["Birthday"], solution_houses[0]["Mother"]],
                    [solution_houses[1]["House"], solution_houses[1]["Name"], solution_houses[1]["Birthday"], solution_houses[1]["Mother"]]
                ]
            }
        }
    print(json.dumps(result))

if __name__ == "__main__":
    main()