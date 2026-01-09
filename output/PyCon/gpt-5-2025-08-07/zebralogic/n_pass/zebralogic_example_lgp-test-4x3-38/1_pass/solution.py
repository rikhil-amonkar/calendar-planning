import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()

    houses = [1, 2, 3, 4]

    # Categories
    names = ["Alice", "Peter", "Arnold", "Eric"]
    mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
    flowers = ["carnations", "roses", "lilies", "daffodils"]

    # Add variables for each attribute with domain of house positions
    for n in names:
        problem.addVariable(n, houses)
    for m in mothers:
        problem.addVariable(m, houses)
    for f in flowers:
        problem.addVariable(f, houses)

    # Uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), mothers)
    problem.addConstraint(AllDifferentConstraint(), flowers)

    # Clues as constraints:

    # 8. Alice is in the third house.
    problem.addConstraint(lambda a: a == 3, ("Alice",))

    # 1. Alice is The person whose mother's name is Kailyn.
    problem.addConstraint(lambda a, k: a == k, ("Alice", "Kailyn"))

    # 5. Arnold is The person whose mother's name is Holly.
    problem.addConstraint(lambda ar, h: ar == h, ("Arnold", "Holly"))

    # 2. The person whose mother's name is Janelle is somewhere to the right of Arnold.
    problem.addConstraint(lambda j, ar: j > ar, ("Janelle", "Arnold"))

    # 3. Peter is somewhere to the right of the person who loves a carnations arrangement.
    problem.addConstraint(lambda p, c: p > c, ("Peter", "carnations"))

    # 4. Eric is the person who loves a bouquet of daffodils.
    problem.addConstraint(lambda e, d: e == d, ("Eric", "daffodils"))

    # 6. The person who loves a carnations arrangement is somewhere to the right of
    #    The person whose mother's name is Holly.
    problem.addConstraint(lambda c, h: c > h, ("carnations", "Holly"))

    # 7. The person who loves the boquet of lilies is directly left of Alice.
    problem.addConstraint(lambda l, a: l == a - 1, ("lilies", "Alice"))

    solutions = problem.getSolutions()

    if not solutions:
        raise RuntimeError("No solution found for the given puzzle constraints.")
    # Assuming unique solution; take the first
    sol = solutions[0]

    # Build rows by house order 1..4
    rows = []
    for h in houses:
        name_at_h = next(n for n in names if sol[n] == h)
        mother_at_h = next(m for m in mothers if sol[m] == h)
        flower_at_h = next(f for f in flowers if sol[f] == h)
        rows.append([str(h), name_at_h, mother_at_h, flower_at_h])

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Flower"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))