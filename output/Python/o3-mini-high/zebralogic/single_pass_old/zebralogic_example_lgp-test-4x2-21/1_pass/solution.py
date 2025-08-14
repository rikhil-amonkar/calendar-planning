#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    # Define the available options for names and house styles.
    names = ["Eric", "Arnold", "Alice", "Peter"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]
    
    solution_found = False
    solution = {}

    # Loop over all possible assignments (permutations) for names and styles.
    for name_perm in itertools.permutations(names):
        # Clue 1: Alice is in the second house (index 1).
        if name_perm[1] != "Alice":
            continue
        for style_perm in itertools.permutations(styles):
            # Clue 5: The person in a Craftsman-style house is Alice.
            craftsman_index = style_perm.index("craftsman")
            if name_perm[craftsman_index] != "Alice":
                continue

            # Clue 2: The person residing in a Victorian house is directly left of Peter.
            victorian_index = style_perm.index("victorian")
            # Victorian cannot be in the last house (house 4, index 3) because there is no house to its right.
            if victorian_index == 3:
                continue
            if name_perm[victorian_index + 1] != "Peter":
                continue

            # Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
            ranch_index = style_perm.index("ranch")
            if name_perm.index("Peter") <= ranch_index:
                continue

            # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
            if name_perm.index("Arnold") <= craftsman_index:
                continue

            # If all constraints are satisfied, we've found the solution.
            solution = {
                "solution": {
                    "header": ["House", "Name", "House style"],
                    "rows": []
                }
            }
            # There are 4 houses numbered 1 to 4.
            for i in range(4):
                # Create a row with house number (as a string), name, and house style.
                solution["solution"]["rows"].append([str(i+1), name_perm[i], style_perm[i]])
            solution_found = True
            break
        if solution_found:
            break

    # Output the solution as a JSON-formatted dictionary.
    print(json.dumps(solution))

if __name__ == "__main__":
    main()