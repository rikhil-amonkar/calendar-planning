import itertools
import json

def solve_puzzle():
    # Define houses and attributes
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    heights = ["short", "very short", "average"]

    solutions = []

    # Iterate over all possible assignments
    for name_perm in itertools.permutations(names):
        # Constraints:
        # 1. Eric is not in the first house.
        if name_perm[0] == "Eric":
            continue
        # 4. Arnold is not in the first house.
        if name_perm[0] == "Arnold":
            continue

        for height_perm in itertools.permutations(heights):
            # 3. The person who is very short is Eric.
            if height_perm.index("very short") != name_perm.index("Eric"):
                continue

            # 2. The person who is very short is somewhere to the left of the person who is short.
            if not (height_perm.index("very short") < height_perm.index("short")):
                continue

            solutions.append((name_perm, height_perm))

    # Expecting a unique solution
    if not solutions:
        raise ValueError("No solution found.")
    # If multiple solutions exist, take the first one deterministically
    name_solution, height_solution = solutions[0]

    # Prepare output
    header = ["House", "Name", "Height"]
    rows = []
    for i, house in enumerate(houses):
        rows.append([str(house), name_solution[i], height_solution[i]])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))