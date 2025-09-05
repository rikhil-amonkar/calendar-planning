import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]

    solutions = []

    # Helper functions
    def houses_between(h1, h2):
        return abs(h1 - h2) - 1

    # Iterate over all permutations of names across houses
    for name_perm in itertools.permutations(names):
        house_to_name = {houses[i]: name_perm[i] for i in range(len(houses))}
        name_to_house = {v: k for k, v in house_to_name.items()}

        # Apply name constraints
        # 1. There are two houses between Eric and Peter. => houses_between == 2
        if houses_between(name_to_house["Eric"], name_to_house["Peter"]) != 2:
            continue

        # 3. Peter is not in the first house.
        if name_to_house["Peter"] == 1:
            continue

        # Iterate over all permutations of occupations across houses
        for occ_perm in itertools.permutations(occupations):
            house_to_occ = {houses[i]: occ_perm[i] for i in range(len(houses))}
            occ_to_house = {v: k for k, v in house_to_occ.items()}

            # Apply occupation constraints
            # 2. The person who is a teacher is Peter.
            if occ_to_house["teacher"] != name_to_house["Peter"]:
                continue

            # 5. The person who is an artist is Alice.
            if occ_to_house["artist"] != name_to_house["Alice"]:
                continue

            # 4. There is one house between the person who is a doctor and Alice.
            if houses_between(occ_to_house["doctor"], name_to_house["Alice"]) != 1:
                continue

            # If all constraints satisfied, record solution
            solutions.append((house_to_name, house_to_occ))

    # Assuming a unique solution as typical in Zebra puzzles
    if not solutions:
        raise ValueError("No solution found with the given constraints.")
    house_to_name, house_to_occ = solutions[0]

    # Prepare output
    header = ["House", "Name", "Occupation"]
    rows = []
    for h in sorted(houses):
        rows.append([str(h), house_to_name[h], house_to_occ[h]])

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