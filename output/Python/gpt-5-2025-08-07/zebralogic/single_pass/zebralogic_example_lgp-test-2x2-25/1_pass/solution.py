import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # Numbered left-to-right (1 is leftmost)
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]

    solutions = []

    # Generate all possible assignments
    for name_perm in itertools.permutations(names, len(houses)):
        name_by_house = {house: name_perm[i] for i, house in enumerate(houses)}

        for vac_perm in itertools.permutations(vacations, len(houses)):
            vac_by_house = {house: vac_perm[i] for i, house in enumerate(houses)}

            # Clue 1: Arnold is somewhere to the right of the person who loves beach vacations.
            house_of_arnold = next(h for h, n in name_by_house.items() if n == "Arnold")
            house_of_beach = next(h for h, v in vac_by_house.items() if v == "beach")
            if not (house_of_arnold > house_of_beach):
                continue

            # If all constraints satisfied, record solution
            solutions.append((name_by_house, vac_by_house))

    # Choose the first solution if multiple (should be unique for this puzzle)
    if not solutions:
        raise ValueError("No solution found.")
    name_by_house, vac_by_house = solutions[0]

    # Prepare JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": [
                [str(h), name_by_house[h], vac_by_house[h]] for h in sorted(houses)
            ],
        }
    }

    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))