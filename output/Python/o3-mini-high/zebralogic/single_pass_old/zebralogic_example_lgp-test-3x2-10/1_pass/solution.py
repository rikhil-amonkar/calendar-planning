#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the puzzle parameters
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    heights = ["short", "very short", "average"]

    solution = None

    # Iterate over all permutations of names and heights for the 3 houses
    for name_perm in itertools.permutations(names):
        # Constraint 1: Eric is not in the first house.
        if name_perm[0] == "Eric":
            continue
        # Constraint 4: Arnold is not in the first house.
        if name_perm[0] == "Arnold":
            continue

        for height_perm in itertools.permutations(heights):
            # Constraint 3: The person who is very short is Eric.
            index_eric = name_perm.index("Eric")
            if height_perm[index_eric] != "very short":
                continue

            # Constraint 2: The person who is very short is somewhere to the left of the person who is short.
            try:
                index_very_short = height_perm.index("very short")
                index_short = height_perm.index("short")
            except ValueError:
                continue
            if index_very_short >= index_short:
                continue

            # All constraints are satisfied; record this solution.
            solution = []
            for i in range(3):
                solution.append({
                    "House": str(houses[i]),
                    "Name": name_perm[i],
                    "height": height_perm[i]
                })
            break  # Found a valid heights permutation for this name assignment
        if solution is not None:
            break  # Found a valid solution

    # Build the output JSON structure.
    output = {
        "solution": {
            "header": ["House", "Name", "height"],
            "rows": [[house["House"], house["Name"], house["height"]] for house in solution]
        }
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()