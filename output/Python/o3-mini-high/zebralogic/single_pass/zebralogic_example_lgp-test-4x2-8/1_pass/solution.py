#!/usr/bin/env python3
import itertools
import json

def solve():
    names = ["Peter", "Arnold", "Alice", "Eric"]
    colors = ["yellow", "green", "red", "white"]
    solution = None

    for name_perm in itertools.permutations(names):
        # Constraint: Peter is in the first house.
        if name_perm[0] != "Peter":
            continue
        for color_perm in itertools.permutations(colors):
            # Constraint: The person whose favorite color is green is in the third house.
            if color_perm[2] != "green":
                continue
            # Constraint: Eric is the person who loves yellow.
            eric_index = name_perm.index("Eric")
            if color_perm[eric_index] != "yellow":
                continue
            # Constraint: There is one house between the person whose favorite color is red and the person who loves yellow.
            red_index = color_perm.index("red")
            yellow_index = color_perm.index("yellow")
            if abs(red_index - yellow_index) != 2:
                continue
            # Constraint: Arnold is directly left of Eric.
            valid_pair = False
            for i in range(len(name_perm) - 1):
                if name_perm[i] == "Arnold" and name_perm[i+1] == "Eric":
                    valid_pair = True
                    break
            if not valid_pair:
                continue
            solution = (name_perm, color_perm)
            break
        if solution is not None:
            break

    if solution:
        name_solution, color_solution = solution
        rows = []
        for i in range(4):
            rows.append([str(i+1), name_solution[i], color_solution[i]])
        output = {"solution": {"header": ["House", "Name", "Color"], "rows": rows}}
    else:
        output = {"solution": {"header": ["House", "Name", "Color"], "rows": []}}
    
    print(json.dumps(output))
    
if __name__ == "__main__":
    solve()