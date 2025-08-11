#!/usr/bin/env python3
import json
import itertools

def main():
    # Define attributes as given in the puzzle
    house_numbers = [1, 2, 3]
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]

    solution = None

    # Generate all possible assignments (permutations) for names and heights.
    for perm_names in itertools.permutations(names):
        for perm_heights in itertools.permutations(heights):
            # Constraint 2: The person who is short is in the first house.
            if perm_heights[0] != "short":
                continue

            # Constraint 3: There is one house between the person who is short and the person who is very short.
            try:
                index_short = perm_heights.index("short")
                index_very_short = perm_heights.index("very short")
            except ValueError:
                continue
            if abs(index_short - index_very_short) != 2:
                continue

            # Constraint 1: Peter is somewhere to the right of Eric.
            index_peter = perm_names.index("Peter")
            index_eric = perm_names.index("Eric")
            if index_peter <= index_eric:
                continue

            # Constraint 4: Arnold and the person who is very short are next to each other.
            index_arnold = perm_names.index("Arnold")
            if abs(index_arnold - index_very_short) != 1:
                continue

            # If all constraints are satisfied, we have a valid solution.
            solution = {
                "header": ["House", "Name", "height"],
                "rows": [[str(i + 1), perm_names[i], perm_heights[i]] for i in range(3)]
            }
            break
        if solution is not None:
            break

    output = {"solution": solution}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()