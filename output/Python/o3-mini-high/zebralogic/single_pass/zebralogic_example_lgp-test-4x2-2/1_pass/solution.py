#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    names = ["Arnold", "Peter", "Eric", "Alice"]
    house_styles = ["victorian", "ranch", "colonial", "craftsman"]
    
    # Houses are indexed 0 to 3 corresponding to positions 1 to 4.
    for perm_names in itertools.permutations(names):
        # Clue 3: Eric is in the third house (index 2).
        # Clue 4: Arnold is in the fourth house (index 3).
        if perm_names[2] != "Eric" or perm_names[3] != "Arnold":
            continue
        for perm_styles in itertools.permutations(house_styles):
            # Clue 1: Eric is in a Craftsman-style house.
            if perm_styles[2] != "craftsman":
                continue
            # Clue 5: The person residing in a Victorian house is Alice.
            valid_victorian = True
            for i in range(4):
                if perm_styles[i] == "victorian" and perm_names[i] != "Alice":
                    valid_victorian = False
                    break
            if not valid_victorian:
                continue
            # Clue 2: The person in a ranch-style home is directly left of the person residing in a Victorian house.
            adjacent_valid = False
            for i in range(3):
                if perm_styles[i] == "ranch" and perm_styles[i+1] == "victorian":
                    adjacent_valid = True
                    break
            if not adjacent_valid:
                continue
            # All constraints satisfied: return this solution.
            return perm_names, perm_styles
    return None, None

def main():
    solution_names, solution_styles = solve_puzzle()
    rows = []
    if solution_names and solution_styles:
        for i in range(4):
            house_number = str(i+1)
            rows.append([house_number, solution_names[i], solution_styles[i]])
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == '__main__':
    main()