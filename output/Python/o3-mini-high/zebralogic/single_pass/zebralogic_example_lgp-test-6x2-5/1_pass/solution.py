#!/usr/bin/env python3
import itertools
import json

def solve():
    names = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]
    solution_found = None

    # Houses are numbered 1 to 6 (index 0 to 5)
    for name_perm in itertools.permutations(names):
        # Constraint 3: Eric is in the second house (index 1)
        if name_perm[1] != "Eric":
            continue
        # Constraint 7 & 4: The person who goes on cultural tours (vacation "cultural") is in the third house
        # and according to clue 7 he is Peter. Thus House3 (index 2) must be "Peter".
        if name_perm[2] != "Peter":
            continue
        # Constraint 2: Eric is somewhere to the right of Alice.
        if name_perm.index("Alice") >= name_perm.index("Eric"):
            continue
        # Constraint 5: Bob is directly left of Arnold.
        if name_perm.index("Bob") + 1 != name_perm.index("Arnold"):
            continue

        for vac_perm in itertools.permutations(vacations):
            # Constraint 4: The cultural tours person is in the third house => House3 (index 2) must be "cultural".
            if vac_perm[2] != "cultural":
                continue
            # Constraint 9: The person who prefers city breaks is in the fourth house => House4 (index 3) must be "city".
            if vac_perm[3] != "city":
                continue
            # Constraint 6: The person who enjoys camping trips is not in the first house.
            if vac_perm[0] == "camping":
                continue
            # Constraint 8: The person who likes going on cruises is Bob.
            cruise_index = vac_perm.index("cruise")
            if name_perm[cruise_index] != "Bob":
                continue
            # Constraint 1: The person who goes on cultural tours is somewhere to the left of the person who loves beach vacations.
            # "cultural" is in house3 (index 2); thus "beach" must appear in a house with index greater than 2.
            if vac_perm.index("beach") <= 2:
                continue

            # All constraints satisfied; build solution.
            solution_rows = []
            for i in range(6):
                # House numbers are strings "1" to "6"
                solution_rows.append([str(i+1), name_perm[i], vac_perm[i]])
            solution_found = solution_rows
            break
        if solution_found:
            break

    if solution_found is None:
        result = {"solution": {"header": ["House", "Name", "vacation"], "rows": []}}
    else:
        result = {"solution": {"header": ["House", "Name", "vacation"], "rows": solution_found}}

    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    solve()