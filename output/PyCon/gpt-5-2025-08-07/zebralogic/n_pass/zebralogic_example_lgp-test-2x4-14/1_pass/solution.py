import json
import sys
import subprocess

# Ensure python-constraint is available
try:
    from constraint import Problem, AllDifferentConstraint
except ImportError:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "python-constraint"])
    from constraint import Problem, AllDifferentConstraint


def build_problem():
    problem = Problem()

    # Houses (left to right)
    houses = [1, 2]

    # Attributes
    names = ["Eric", "Arnold"]
    styles = ["victorian", "colonial"]
    smoothies = ["cherry", "desert"]
    pets = ["dog", "cat"]

    def v(category, item):
        return f"{category}_{item}"

    # Variables: each item mapped to a house number
    for item in names:
        problem.addVariable(v("Name", item), houses)
    for item in styles:
        problem.addVariable(v("HouseStyle", item), houses)
    for item in smoothies:
        problem.addVariable(v("Smoothie", item), houses)
    for item in pets:
        problem.addVariable(v("Pet", item), houses)

    # Uniqueness within each category
    problem.addConstraint(AllDifferentConstraint(), [v("Name", i) for i in names])
    problem.addConstraint(AllDifferentConstraint(), [v("HouseStyle", i) for i in styles])
    problem.addConstraint(AllDifferentConstraint(), [v("Smoothie", i) for i in smoothies])
    problem.addConstraint(AllDifferentConstraint(), [v("Pet", i) for i in pets])

    # Clues:
    # 1. The person who likes Cherry smoothies is the person who owns a dog.
    problem.addConstraint(lambda sc, pd: sc == pd, (v("Smoothie", "cherry"), v("Pet", "dog")))

    # 2. The person residing in a Victorian house is the person who owns a dog.
    problem.addConstraint(lambda sv, pd: sv == pd, (v("HouseStyle", "victorian"), v("Pet", "dog")))

    # 3. The person residing in a Victorian house is somewhere to the left of Eric.
    problem.addConstraint(lambda sv, ne: sv < ne, (v("HouseStyle", "victorian"), v("Name", "Eric")))

    return problem, houses, names, styles, smoothies, pets, v


def main():
    problem, houses, names, styles, smoothies, pets, v = build_problem()
    solutions = problem.getSolutions()

    header = ["House", "Name", "HouseStyle", "Smoothie", "Pet"]
    rows = []

    if solutions:
        sol = solutions[0]  # Expecting a unique solution

        for h in sorted(houses):
            name = next(n for n in names if sol[v("Name", n)] == h)
            style = next(s for s in styles if sol[v("HouseStyle", s)] == h)
            smoothie = next(s for s in smoothies if sol[v("Smoothie", s)] == h)
            pet = next(p for p in pets if sol[v("Pet", p)] == h)
            rows.append([str(h), name, style, smoothie, pet])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result))


if __name__ == "__main__":
    main()