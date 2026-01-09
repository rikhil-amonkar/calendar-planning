import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    # Attributes
    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]

    problem = Problem()

    # Variables: each name and each height maps to a house number (1..5)
    for name in names:
        problem.addVariable(name, houses)

    height_varnames = {h: f"Height::{h}" for h in heights}
    for h_label, varname in height_varnames.items():
        problem.addVariable(varname, houses)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), list(height_varnames.values()))

    # Clues:
    # 1. The person who is short is in the second house.
    problem.addConstraint(lambda s: s == 2, [height_varnames["short"]])

    # 2. Peter is directly left of Bob.
    problem.addConstraint(lambda p, b: p + 1 == b, ["Peter", "Bob"])

    # 3. Eric is somewhere to the left of Peter.
    problem.addConstraint(lambda e, p: e < p, ["Eric", "Peter"])

    # 4. The person who is very tall is directly left of Peter.
    problem.addConstraint(lambda vt, p: vt + 1 == p, [height_varnames["very tall"], "Peter"])

    # 5. Alice is directly left of the person who has an average height.
    problem.addConstraint(lambda a, avg: a + 1 == avg, ["Alice", height_varnames["average"]])

    # 6. The person who is short and the person who is very short are next to each other.
    problem.addConstraint(lambda s, vs: abs(s - vs) == 1, [height_varnames["short"], height_varnames["very short"]])

    # 7. The person who has an average height is in the fifth house.
    problem.addConstraint(lambda avg: avg == 5, [height_varnames["average"]])

    solutions = problem.getSolutions()

    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    # Assuming unique solution; take the first
    sol = solutions[0]

    # Build house to name and height mappings
    house_to_name = {sol[name]: name for name in names}
    house_to_height = {sol[varname]: label for label, varname in height_varnames.items()}

    rows = []
    for house in houses:
        rows.append([str(house), house_to_name[house], house_to_height[house]])

    output = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()