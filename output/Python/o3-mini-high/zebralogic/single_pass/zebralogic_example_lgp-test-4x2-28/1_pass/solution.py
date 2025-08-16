#!/usr/bin/env python3
import json
import itertools

def solve_zebra_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Alice", "Arnold", "Peter", "Eric"]
    hair_colors = ["black", "blonde", "brown", "red"]
    
    solutions = []
    
    # Iterate over all possible permutations of names, ensuring Alice is in the first house.
    for name_perm in itertools.permutations(names):
        if name_perm[0] != "Alice":
            continue
        # Clue 2: Alice and Arnold are next to each other.
        if abs(name_perm.index("Alice") - name_perm.index("Arnold")) != 1:
            continue
        
        # Iterate over all permutations of hair colors.
        for hair_perm in itertools.permutations(hair_colors):
            # Clue 4: The person with black hair is not in the first house.
            if hair_perm[0] == "black":
                continue
            # Clue 3: Eric is the person who has brown hair.
            if hair_perm[name_perm.index("Eric")] != "brown":
                continue
            # Clue 1: Eric is directly left of the person who has blonde hair.
            pos_eric = name_perm.index("Eric")
            # Eric cannot be in the last house if he is to the left of someone.
            if pos_eric == len(houses) - 1:
                continue
            if hair_perm[pos_eric + 1] != "blonde":
                continue
            
            solutions.append((name_perm, hair_perm))
    
    # Assume there is exactly one solution.
    if solutions:
        sol_names, sol_hairs = solutions[0]
        solution_rows = []
        for i in range(len(houses)):
            # House numbers are 1-indexed and converted to string.
            solution_rows.append([str(i+1), sol_names[i], sol_hairs[i]])
        return solution_rows
    return None

if __name__ == "__main__":
    solution = solve_zebra_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "HairColor"],
            "rows": solution
        }
    }
    print(json.dumps(output))