import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define domains
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["victorian", "ranch", "colonial", "craftsman"]

    # Initialize problem
    problem = Problem()

    # Variables: positions of each name and each style
    for n in names:
        problem.addVariable(n, houses)
    for s in styles:
        problem.addVariable(s, houses)

    # Uniqueness constraints
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), styles)

    # Clues:
    # 1. Eric is the person in a Craftsman-style house.
    problem.addConstraint(lambda e, c: e == c, ("Eric", "craftsman"))

    # 2. Ranch is directly left of Victorian.
    problem.addConstraint(lambda r, v: r == v - 1, ("ranch", "victorian"))

    # 3. Eric is in the third house.
    problem.addConstraint(lambda e: e == 3, ("Eric",))

    # 4. Arnold is in the fourth house.
    problem.addConstraint(lambda a: a == 4, ("Arnold",))

    # 5. The person residing in a Victorian house is Alice.
    problem.addConstraint(lambda v, a: v == a, ("victorian", "Alice"))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    sol = solutions[0]

    # Build output rows ordered by house number
    rows = []
    for h in sorted(houses):
        # Find the name and style at house h
        name_at_h = next(n for n in names if sol[n] == h)
        style_at_h = next(s for s in styles if sol[s] == h)
        rows.append([str(h), name_at_h, style_at_h])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }

    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()