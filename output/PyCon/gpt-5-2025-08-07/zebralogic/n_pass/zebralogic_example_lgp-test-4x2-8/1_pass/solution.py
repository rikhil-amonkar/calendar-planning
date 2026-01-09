import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define attributes
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Alice", "Eric"]
    colors = ["yellow", "green", "red", "white"]

    # Initialize problem
    problem = Problem()

    # Create variables: position (house number) for each name and color
    name_vars = {name: f"N_{name}" for name in names}
    color_vars = {color: f"C_{color}" for color in colors}

    for var in name_vars.values():
        problem.addVariable(var, houses)
    for var in color_vars.values():
        problem.addVariable(var, houses)

    # All different constraints within categories
    problem.addConstraint(AllDifferentConstraint(), list(name_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(color_vars.values()))

    # Clues:
    # 1. The person whose favorite color is green is in the third house.
    problem.addConstraint(lambda g: g == 3, [color_vars["green"]])

    # 2. Peter is in the first house.
    problem.addConstraint(lambda p: p == 1, [name_vars["Peter"]])

    # 3. There is one house between the person whose favorite color is red and the person who loves yellow.
    problem.addConstraint(lambda r, y: abs(r - y) == 2, [color_vars["red"], color_vars["yellow"]])

    # 4. Arnold is directly left of Eric.
    problem.addConstraint(lambda a, e: a + 1 == e, [name_vars["Arnold"], name_vars["Eric"]])

    # 5. Eric is the person who loves yellow.
    problem.addConstraint(lambda e, y: e == y, [name_vars["Eric"], color_vars["yellow"]])

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found")

    sol = solutions[0]

    # Build output rows in house order
    rows = []
    for h in sorted(houses):
        # Find the name and color at house h
        name_at_h = next(name for name in names if sol[name_vars[name]] == h)
        color_at_h = next(color for color in colors if sol[color_vars[color]] == h)
        rows.append([str(h), name_at_h, color_at_h])

    output = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result))