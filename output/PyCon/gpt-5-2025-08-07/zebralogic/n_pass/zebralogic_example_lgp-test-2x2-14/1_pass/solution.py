import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define domains
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]

    # Initialize problem
    problem = Problem()

    # Variables map each attribute to a house number
    name_vars = [f"Name:{n}" for n in names]
    food_vars = [f"Food:{f}" for f in foods]

    for var in name_vars + food_vars:
        problem.addVariable(var, houses)

    # Uniqueness constraints per category
    problem.addConstraint(AllDifferentConstraint(), name_vars)
    problem.addConstraint(AllDifferentConstraint(), food_vars)

    # Clue 1: The person who is a pizza lover is in the second house.
    problem.addConstraint(lambda h: h == 2, ["Food:pizza"])

    # Clue 2: Arnold is not in the first house.
    problem.addConstraint(lambda h: h != 1, ["Name:Arnold"])

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")
    sol = solutions[0]

    # Invert mappings to get attributes per house
    name_by_house = {sol[f"Name:{n}"]: n for n in names}
    food_by_house = {sol[f"Food:{f}"]: f for f in foods}

    # Build JSON output
    rows = []
    for h in sorted(houses):
        rows.append([str(h), name_by_house[h], food_by_house[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))