#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    favorite_sports = ["basketball", "soccer"]
    favorite_smoothies = ["desert", "cherry"]

    solution = None

    for perm_names in itertools.permutations(names):
        for perm_hair in itertools.permutations(hair_colors):
            for perm_sport in itertools.permutations(favorite_sports):
                for perm_smoothie in itertools.permutations(favorite_smoothies):
                    valid = True
                    
                    # Constraint 1: The Desert smoothie lover is Arnold.
                    for i in range(2):
                        if perm_smoothie[i] == "desert" and perm_names[i] != "Arnold":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Constraint 2: The person who has brown hair is the person who loves basketball.
                    for i in range(2):
                        if (perm_hair[i] == "brown" and perm_sport[i] != "basketball") or (perm_sport[i] == "basketball" and perm_hair[i] != "brown"):
                            valid = False
                            break
                    if not valid:
                        continue

                    # Constraint 3: Arnold is somewhere to the left of the person who has black hair.
                    index_arnold = perm_names.index("Arnold")
                    index_black = perm_hair.index("black")
                    if index_arnold >= index_black:
                        valid = False
                    if not valid:
                        continue

                    # Build the solution rows for each house (House 1 is the leftmost).
                    rows = []
                    for i in range(2):
                        row = [str(i+1), perm_names[i], perm_hair[i], perm_sport[i], perm_smoothie[i]]
                        rows.append(row)
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Hair Color", "Favorite Sport", "Favorite Smoothie"],
                            "rows": rows
                        }
                    }
                    return solution
    return solution

if __name__ == "__main__":
    sol = solve_puzzle()
    print(json.dumps(sol))