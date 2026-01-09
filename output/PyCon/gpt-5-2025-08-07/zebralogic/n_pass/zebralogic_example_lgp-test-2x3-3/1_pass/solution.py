import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2]

    names = ["Arnold", "Eric"]
    foods = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]

    problem = Problem()

    # Variables: position (house number) for each attribute
    for n in names:
        problem.addVariable(f"Name_{n}", houses)
    for f in foods:
        problem.addVariable(f"Food_{f}", houses)
    for m in mothers:
        problem.addVariable(f"Mother_{m}", houses)

    # All different within each category
    problem.addConstraint(AllDifferentConstraint(), [f"Name_{n}" for n in names])
    problem.addConstraint(AllDifferentConstraint(), [f"Food_{f}" for f in foods])
    problem.addConstraint(AllDifferentConstraint(), [f"Mother_{m}" for m in mothers])

    # Clue 1: The person who loves eating grilled cheese is directly left of the pizza lover.
    problem.addConstraint(
        lambda g, p: g == p - 1,
        ("Food_grilled cheese", "Food_pizza")
    )

    # Clue 2: Arnold is not in the second house.
    problem.addConstraint(lambda a: a != 2, ("Name_Arnold",))

    # Clue 3: Arnold is the person whose mother's name is Holly.
    problem.addConstraint(lambda a, h: a == h, ("Name_Arnold", "Mother_Holly"))

    solution = problem.getSolution()
    if not solution:
        raise ValueError("No solution found for the given puzzle.")

    # Build rows for houses 1..2
    rows = []
    for h in sorted(houses):
        name_at_house = next(n for n in names if solution[f"Name_{n}"] == h)
        food_at_house = next(f for f in foods if solution[f"Food_{f}"] == h)
        mother_at_house = next(m for m in mothers if solution[f"Mother_{m}"] == h)
        rows.append([str(h), name_at_house, food_at_house, mother_at_house])

    output = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()