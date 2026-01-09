import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Houses
    houses = [1, 2]

    # Attributes
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]

    # Set up the problem
    problem = Problem()

    # Add variables: each attribute value maps to a house number
    for item in names + hair_colors + sports + smoothies:
        problem.addVariable(item, houses)

    # Uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), hair_colors)
    problem.addConstraint(AllDifferentConstraint(), sports)
    problem.addConstraint(AllDifferentConstraint(), smoothies)

    # Clue 1: The Desert smoothie lover is Arnold.
    problem.addConstraint(lambda a, d: a == d, ("Arnold", "desert"))

    # Clue 2: The person who has brown hair is the person who loves basketball.
    problem.addConstraint(lambda br, bb: br == bb, ("brown", "basketball"))

    # Clue 3: Arnold is somewhere to the left of the person who has black hair.
    problem.addConstraint(lambda a, b: a < b, ("Arnold", "black"))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    sol = solutions[0]

    # Build output rows in house order
    rows = []
    for h in sorted(houses):
        house_name = next(n for n in names if sol[n] == h)
        house_hair = next(c for c in hair_colors if sol[c] == h)
        house_sport = next(s for s in sports if sol[s] == h)
        house_smoothie = next(m for m in smoothies if sol[m] == h)
        rows.append([str(h), house_name, house_hair, house_sport, house_smoothie])

    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    output = solve_puzzle()
    print(json.dumps(output, ensure_ascii=False, indent=2))