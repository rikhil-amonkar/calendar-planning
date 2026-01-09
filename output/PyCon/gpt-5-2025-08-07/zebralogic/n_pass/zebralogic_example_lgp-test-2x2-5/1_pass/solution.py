import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    styles = ["victorian", "colonial"]

    problem = Problem()

    # Variables: map each attribute value to a house number
    problem.addVariables(names, houses)
    problem.addVariables(styles, houses)

    # Uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), styles)

    # Clue 1: Victorian is to the left of Colonial
    problem.addConstraint(lambda v, c: v < c, ("victorian", "colonial"))

    # Clue 2: Eric is in the first house
    problem.addConstraint(lambda e: e == 1, ("Eric",))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    solution = solutions[0]

    # Build rows ordered by house number
    rows = []
    for h in sorted(houses):
        name_at_house = next(n for n in names if solution[n] == h)
        style_at_house = next(s for s in styles if solution[s] == h)
        rows.append([str(h), name_at_house, style_at_house])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))