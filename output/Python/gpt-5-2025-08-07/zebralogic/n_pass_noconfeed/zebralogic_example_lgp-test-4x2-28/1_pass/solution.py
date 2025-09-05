import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3, 4]
    names = ["Alice", "Arnold", "Peter", "Eric"]
    hair_colors = ["black", "blonde", "brown", "red"]

    solutions = []

    # Helper: index maps house -> 0-based index
    # We'll use permutations of names and hair_colors assigned to house indices [0..3]
    for name_perm in itertools.permutations(names):
        # Constraint 5: Alice is in the first house.
        if name_perm[0] != "Alice":
            continue

        # Constraint 2: Alice and Arnold are next to each other.
        house_of = {name_perm[i]: i + 1 for i in range(4)}
        if abs(house_of["Alice"] - house_of["Arnold"]) != 1:
            continue

        # Now assign hair colors
        for hair_perm in itertools.permutations(hair_colors):
            # Constraint 4: The person who has black hair is not in the first house.
            if hair_perm[0] == "black":
                continue

            # Constraint 3: Eric is the person who has brown hair.
            eric_house_idx = house_of["Eric"] - 1
            if hair_perm[eric_house_idx] != "brown":
                continue

            # Constraint 1: Eric is directly left of the person who has blonde hair.
            if eric_house_idx == 3:
                continue  # cannot be directly left if in last house
            if hair_perm[eric_house_idx + 1] != "blonde":
                continue

            # All constraints satisfied; build solution
            rows = []
            for h in houses:
                name = name_perm[h - 1]
                hair = hair_perm[h - 1]
                rows.append([str(h), name, hair])

            solutions.append({
                "solution": {
                    "header": ["House", "Name", "HairColor"],
                    "rows": rows
                }
            })

    # Assuming unique solution; if multiple, take the first
    if solutions:
        return solutions[0]
    else:
        # In case no solution found, still return structure with empty rows for robustness
        return {
            "solution": {
                "header": ["House", "Name", "HairColor"],
                "rows": []
            }
        }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))