import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = range(1, 6)

    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]

    problem = Problem()

    # Variables: each name and each child maps to a house position 1..5
    for n in names:
        problem.addVariable(n, houses)
    for c in children:
        problem.addVariable(c, houses)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), children)

    # Clues:
    # 1. Bob is somewhere to the left of the person's child is named Samantha.
    problem.addConstraint(lambda bob, sam: bob < sam, ("Bob", "Samantha"))

    # 2. The person who is the mother of Timothy is somewhere to the left of Samantha.
    problem.addConstraint(lambda tim, sam: tim < sam, ("Timothy", "Samantha"))

    # 3. Fred is in the second house.
    problem.addConstraint(lambda f: f == 2, ("Fred",))

    # 4. There is one house between Alice and Samantha (difference of 2).
    problem.addConstraint(lambda alice, sam: abs(alice - sam) == 2, ("Alice", "Samantha"))

    # 5. Eric is not in the third house.
    problem.addConstraint(lambda e: e != 3, ("Eric",))

    # 6. Bob is not in the third house.
    problem.addConstraint(lambda b: b != 3, ("Bob",))

    # 7. Fred is directly left of Bella.
    problem.addConstraint(lambda f, b: f + 1 == b, ("Fred", "Bella"))

    # 8. Samantha is somewhere to the left of Peter.
    problem.addConstraint(lambda sam, p: sam < p, ("Samantha", "Peter"))

    solution = problem.getSolution()
    if not solution:
        raise RuntimeError("No solution found for the given puzzle.")

    # Invert mappings to get house -> Name and house -> Children
    name_by_pos = {solution[n]: n for n in names}
    child_by_pos = {solution[c]: c for c in children}

    rows = []
    for h in range(1, 6):
        rows.append([str(h), name_by_pos[h], child_by_pos[h]])

    output = {
        "solution": {
            "header": ["House", "Name", "Children"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))