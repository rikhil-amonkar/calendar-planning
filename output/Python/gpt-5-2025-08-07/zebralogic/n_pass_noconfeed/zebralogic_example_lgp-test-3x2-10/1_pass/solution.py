import itertools
import json

def solve_puzzle():
    # Define entities
    houses = [1, 2, 3]  # Left (1) to right (3)
    names = ["Eric", "Arnold", "Peter"]
    heights = ["short", "very short", "average"]

    solutions = []

    # Enumerate all possible assignments
    for name_perm in itertools.permutations(names):
        # Clue 1: Eric is not in the first house.
        if name_perm[0] == "Eric":
            continue

        # Clue 4: Arnold is not in the first house.
        if name_perm[0] == "Arnold":
            continue

        for height_perm in itertools.permutations(heights):
            # Clue 3: The person who is very short is Eric.
            idx_very_short = height_perm.index("very short")
            idx_eric = name_perm.index("Eric")
            if idx_very_short != idx_eric:
                continue

            # Clue 2: The very short person is somewhere to the left of the short person.
            if idx_very_short >= height_perm.index("short"):
                continue

            # All constraints satisfied; build solution rows
            rows = []
            for i, house in enumerate(houses):
                rows.append([str(house), name_perm[i], height_perm[i]])

            solutions.append({
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": rows
                }
            })

    # Output the first solution found (puzzle is expected to have a unique solution)
    return solutions[0] if solutions else {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": []
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))