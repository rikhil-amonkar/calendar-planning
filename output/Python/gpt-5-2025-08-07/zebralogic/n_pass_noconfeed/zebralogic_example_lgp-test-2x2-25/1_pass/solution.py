import json
from itertools import permutations

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # Left to right
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]

    solutions = []

    # Try all combinations (permutations) of assignments
    for name_perm in permutations(names):
        name_by_house = {houses[i]: name_perm[i] for i in range(len(houses))}
        # Inverse mapping for convenience
        house_of_name = {name_by_house[h]: h for h in houses}

        for vac_perm in permutations(vacations):
            vac_by_house = {houses[i]: vac_perm[i] for i in range(len(houses))}
            house_of_vac = {vac_by_house[h]: h for h in houses}

            # Apply constraints:

            # 1) "Arnold is somewhere to the right of the person who loves beach vacations."
            #    Right means higher house number.
            if house_of_name["Arnold"] <= house_of_vac["beach"]:
                continue

            # All constraints satisfied; store solution
            solutions.append((name_by_house, vac_by_house))

    # Choose the first solution (there should be exactly one for this puzzle)
    if not solutions:
        raise ValueError("No solution found.")
    name_by_house, vac_by_house = solutions[0]

    # Build the required JSON structure
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": [
                [str(h), name_by_house[h], vac_by_house[h]] for h in houses
            ]
        }
    }
    return result

if __name__ == "__main__":
    solution_json = solve_puzzle()
    print(json.dumps(solution_json, ensure_ascii=False))