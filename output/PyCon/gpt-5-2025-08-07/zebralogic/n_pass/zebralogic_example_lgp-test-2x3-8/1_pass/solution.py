import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2]

    names = ["Arnold", "Eric"]
    birthdays = ["april", "sept"]
    mothers = ["Aniya", "Holly"]

    problem = Problem()

    # Variables: map each attribute value to a house number
    for n in names:
        problem.addVariable(f"Name_{n}", houses)
    for b in birthdays:
        problem.addVariable(f"Birthday_{b}", houses)
    for m in mothers:
        problem.addVariable(f"Mother_{m}", houses)

    # Uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), [f"Name_{n}" for n in names])
    problem.addConstraint(AllDifferentConstraint(), [f"Birthday_{b}" for b in birthdays])
    problem.addConstraint(AllDifferentConstraint(), [f"Mother_{m}" for m in mothers])

    # Clue 1: Eric is somewhere to the left of the person whose mother's name is Holly.
    problem.addConstraint(lambda e, h: e < h, ("Name_Eric", "Mother_Holly"))

    # Clue 2: The person whose birthday is in April is in the first house.
    problem.addConstraint(lambda a: a == 1, ("Birthday_april",))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found")

    sol = solutions[0]

    # Build rows per house
    rows = []
    for h in sorted(houses):
        # Find the attribute values that map to this house
        name = next(n for n in names if sol[f"Name_{n}"] == h)
        birthday = next(b for b in birthdays if sol[f"Birthday_{b}"] == h)
        mother = next(m for m in mothers if sol[f"Mother_{m}"] == h)
        rows.append([str(h), name, birthday, mother])

    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()