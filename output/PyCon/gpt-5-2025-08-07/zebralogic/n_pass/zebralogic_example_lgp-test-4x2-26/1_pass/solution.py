import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define entities
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]

    # Setup problem
    problem = Problem()

    # Variables: each name and each occupation is assigned to a house (1..4)
    problem.addVariables(names, houses)
    problem.addConstraint(AllDifferentConstraint(), names)

    problem.addVariables(occupations, houses)
    problem.addConstraint(AllDifferentConstraint(), occupations)

    # Clue 1: There are two houses between Eric and Peter. (difference of 3)
    problem.addConstraint(lambda e, p: abs(e - p) == 3, ("Eric", "Peter"))

    # Clue 2: The person who is a teacher is Peter.
    problem.addConstraint(lambda t, p: t == p, ("teacher", "Peter"))

    # Clue 3: Peter is not in the first house.
    problem.addConstraint(lambda p: p != 1, ("Peter",))

    # Clue 4: There is one house between the doctor and Alice. (difference of 2)
    problem.addConstraint(lambda d, a: abs(d - a) == 2, ("doctor", "Alice"))

    # Clue 5: The person who is an artist is Alice.
    problem.addConstraint(lambda art, a: art == a, ("artist", "Alice"))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    s = solutions[0]

    # Build house -> name and house -> occupation mappings
    name_by_house = {s[name]: name for name in names}
    occ_by_house = {s[occ]: occ for occ in occupations}

    # Prepare JSON output
    result = {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": []
        }
    }

    for h in sorted(houses):
        row = [str(h), name_by_house[h], occ_by_house[h]]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()