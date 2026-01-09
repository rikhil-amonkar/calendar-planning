import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define attributes
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    heights = ["short", "very short", "average"]

    # Initialize problem
    problem = Problem()

    # Variables: house positions for each name
    for name in names:
        problem.addVariable(f"HouseOf_{name}", houses)
    problem.addConstraint(AllDifferentConstraint(), [f"HouseOf_{n}" for n in names])

    # Variables: house positions for each height
    for h in heights:
        problem.addVariable(f"HouseOfHeight_{h}", houses)
    problem.addConstraint(AllDifferentConstraint(), [f"HouseOfHeight_{h}" for h in heights])

    # Constraints based on clues
    # 1. Eric is not in the first house.
    problem.addConstraint(lambda e: e != 1, ("HouseOf_Eric",))
    # 2. The person who is very short is somewhere to the left of the person who is short.
    problem.addConstraint(lambda v, s: v < s, ("HouseOfHeight_very short", "HouseOfHeight_short"))
    # 3. The person who is very short is Eric.
    problem.addConstraint(lambda e, v: e == v, ("HouseOf_Eric", "HouseOfHeight_very short"))
    # 4. Arnold is not in the first house.
    problem.addConstraint(lambda a: a != 1, ("HouseOf_Arnold",))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    sol = solutions[0]

    # Build mappings from house to attributes
    house_to_name = {}
    for name in names:
        house_to_name[sol[f"HouseOf_{name}"]] = name

    house_to_height = {}
    for h in heights:
        house_to_height[sol[f"HouseOfHeight_{h}"]] = h

    # Prepare rows in order of houses 1..3
    rows = []
    for house in houses:
        rows.append([str(house), house_to_name[house], house_to_height[house]])

    # Output JSON
    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()