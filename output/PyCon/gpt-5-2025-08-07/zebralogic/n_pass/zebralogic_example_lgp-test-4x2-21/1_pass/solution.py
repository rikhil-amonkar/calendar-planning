import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define attributes
    houses = [1, 2, 3, 4]
    names = ["Eric", "Arnold", "Alice", "Peter"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]

    # Set up the constraint problem
    problem = Problem()
    problem.addVariables(names, houses)
    problem.addVariables(styles, houses)

    # Uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), styles)

    # Clue 1: Alice is in the second house.
    problem.addConstraint(lambda a: a == 2, ("Alice",))

    # Clue 2: The person residing in a Victorian house is directly left of Peter.
    problem.addConstraint(lambda v, p: v == p - 1, ("victorian", "Peter"))

    # Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
    problem.addConstraint(lambda p, r: p > r, ("Peter", "ranch"))

    # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
    problem.addConstraint(lambda a, c: a > c, ("Arnold", "craftsman"))

    # Clue 5: The person in a Craftsman-style house is Alice.
    problem.addConstraint(lambda a, c: a == c, ("Alice", "craftsman"))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    sol = solutions[0]

    # Build output rows in house order
    pos_to_name = {sol[n]: n for n in names}
    pos_to_style = {sol[s]: s for s in styles}

    rows = []
    for h in houses:
        rows.append([str(h), pos_to_name[h], pos_to_style[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))