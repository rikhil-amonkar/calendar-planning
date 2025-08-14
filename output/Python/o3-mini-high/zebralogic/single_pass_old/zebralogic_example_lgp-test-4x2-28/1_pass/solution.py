#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    names = ["Alice", "Arnold", "Peter", "Eric"]
    hair_colors = ["black", "blonde", "brown", "red"]

    # Iterate through all possible assignments of names and hair colors to 4 houses.
    for name_perm in itertools.permutations(names):
        # Clue 5: Alice is in the first house.
        if name_perm[0] != "Alice":
            continue

        # Clue 2: Alice and Arnold are next to each other.
        alice_index = name_perm.index("Alice")
        arnold_index = name_perm.index("Arnold")
        if abs(alice_index - arnold_index) != 1:
            continue

        for hair_perm in itertools.permutations(hair_colors):
            # Clue 4: The person who has black hair is not in the first house.
            if hair_perm[0] == "black":
                continue

            houses = []
            for i in range(4):
                houses.append({
                    "House": str(i+1),
                    "Name": name_perm[i],
                    "Hair Color": hair_perm[i]
                })

            # Clue 1: Eric is directly left of the person who has blonde hair.
            eric_index = name_perm.index("Eric")
            if eric_index == 3:  # Eric cannot be in the last house.
                continue
            if hair_perm[eric_index + 1] != "blonde":
                continue

            # Clue 3: Eric is the person who has brown hair.
            if hair_perm[eric_index] != "brown":
                continue

            # All constraints satisfied, return the solution.
            return houses
    return None

def main():
    solution_houses = solve_puzzle()
    if solution_houses is None:
        output = {"solution": {"header": ["House", "Name", "Hair Color"], "rows": []}}
    else:
        rows = []
        for house in solution_houses:
            rows.append([house["House"], house["Name"], house["Hair Color"]])
        output = {"solution": {"header": ["House", "Name", "Hair Color"], "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()