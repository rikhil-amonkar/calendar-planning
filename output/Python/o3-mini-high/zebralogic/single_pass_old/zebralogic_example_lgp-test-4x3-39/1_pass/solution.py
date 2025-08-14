#!/usr/bin/env python3
import itertools
import json

def solve():
    names = ["Eric", "Alice", "Peter", "Arnold"]
    hair_colors = ["blonde", "black", "red", "brown"]
    favorite_sports = ["swimming", "soccer", "basketball", "tennis"]

    # Iterate over all possible assignments using permutations.
    for names_perm in itertools.permutations(names):
        for hair_perm in itertools.permutations(hair_colors):
            for sports_perm in itertools.permutations(favorite_sports):
                # Constraint 1: The person who loves soccer is not in the second house.
                if sports_perm[1] == "soccer":
                    continue

                # Constraint 2: Eric is the person who has blonde hair.
                try:
                    idx_eric = names_perm.index("Eric")
                except ValueError:
                    continue
                if hair_perm[idx_eric] != "blonde":
                    continue

                # Constraint 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
                idx_basketball = sports_perm.index("basketball")
                idx_blonde = hair_perm.index("blonde")
                if idx_blonde <= idx_basketball:
                    continue

                # Constraint 4: The person who has black hair is the person who loves tennis.
                valid = True
                for i in range(4):
                    if hair_perm[i] == "black" and sports_perm[i] != "tennis":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 5: Arnold is somewhere to the left of the person who has red hair.
                idx_arnold = names_perm.index("Arnold")
                try:
                    idx_red = hair_perm.index("red")
                except ValueError:
                    continue
                if idx_arnold >= idx_red:
                    continue

                # Constraint 6: Alice is the person who loves swimming.
                idx_alice = names_perm.index("Alice")
                if sports_perm[idx_alice] != "swimming":
                    continue

                # Constraint 7: The person who has red hair is directly left of the person who has black hair.
                found_red_black = False
                for i in range(3):
                    if hair_perm[i] == "red" and hair_perm[i+1] == "black":
                        found_red_black = True
                        break
                if not found_red_black:
                    continue

                # If all constraints are satisfied, build and return the solution.
                solution = {
                    "solution": {
                        "header": ["House", "Name", "hair color", "favorite sport"],
                        "rows": []
                    }
                }
                for i in range(4):
                    row = [str(i+1), names_perm[i], hair_perm[i], sports_perm[i]]
                    solution["solution"]["rows"].append(row)
                return solution
    return None

def main():
    result = solve()
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()