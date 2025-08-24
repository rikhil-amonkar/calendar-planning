import json
from itertools import permutations

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3, 4]  # left to right
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]

    solutions = []

    for name_perm in permutations(names):
        pos_by_name = {name: idx for idx, name in enumerate(name_perm)}  # index 0..3 corresponds to house 1..4

        # Clue 1: There are two houses between Eric and Peter -> positions differ by 3 (i.e., houses 1 and 4)
        if abs(pos_by_name["Eric"] - pos_by_name["Peter"]) != 3:
            continue

        # Clue 3: Peter is not in the first house
        if pos_by_name["Peter"] == 0:
            continue

        for occ_perm in permutations(occupations):
            pos_by_occ = {occ: idx for idx, occ in enumerate(occ_perm)}

            # Clue 2: The person who is a teacher is Peter
            if pos_by_occ["teacher"] != pos_by_name["Peter"]:
                continue

            # Clue 5: The person who is an artist is Alice
            if pos_by_occ["artist"] != pos_by_name["Alice"]:
                continue

            # Clue 4: There is one house between the person who is a doctor and Alice
            if abs(pos_by_occ["doctor"] - pos_by_name["Alice"]) != 2:
                continue

            # If all constraints satisfied, record the solution
            rows = []
            for i, house in enumerate(houses):
                rows.append([str(house), name_perm[i], occ_perm[i]])
            solutions.append(rows)

    # Assuming a unique solution per the puzzle
    if not solutions:
        raise ValueError("No solution found.")
    if len(solutions) > 1:
        # Still output the first, but puzzle implies uniqueness
        rows = solutions[0]
    else:
        rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()