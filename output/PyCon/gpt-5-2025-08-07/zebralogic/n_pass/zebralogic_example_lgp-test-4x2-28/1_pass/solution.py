import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define entities
    houses = [1, 2, 3, 4]
    names = ["Alice", "Arnold", "Peter", "Eric"]
    hair_colors = ["black", "blonde", "brown", "red"]

    # Create problem
    problem = Problem()

    # Variables: each name and hair color is mapped to a house number
    for name in names:
        problem.addVariable(name, houses)
    for color in hair_colors:
        problem.addVariable(color, houses)

    # AllDifferent constraints
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), hair_colors)

    # Clues:
    # 1. Eric is directly left of the person who has blonde hair.
    problem.addConstraint(lambda eric, blonde: eric == blonde - 1, ("Eric", "blonde"))
    # 2. Alice and Arnold are next to each other.
    problem.addConstraint(lambda alice, arnold: abs(alice - arnold) == 1, ("Alice", "Arnold"))
    # 3. Eric is the person who has brown hair.
    problem.addConstraint(lambda eric, brown: eric == brown, ("Eric", "brown"))
    # 4. The person who has black hair is not in the first house.
    problem.addConstraint(lambda black: black != 1, ("black",))
    # 5. Alice is in the first house.
    problem.addConstraint(lambda alice: alice == 1, ("Alice",))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    sol = solutions[0]

    # Build output rows in house order
    rows = []
    for h in houses:
        name_at_house = next(n for n in names if sol[n] == h)
        color_at_house = next(c for c in hair_colors if sol[c] == h)
        rows.append([str(h), name_at_house, color_at_house])

    result = {
        "solution": {
            "header": ["House", "Name", "HairColor"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()