import json
from constraint import Problem, AllDifferentConstraint

def var_key(category, value):
    return f"{category}_{value.replace(' ', '_')}"

def solve_puzzle():
    # Define attributes
    houses = range(1, 6)
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    heights = ["average", "very short", "short", "very tall", "tall"]

    # Create variable names
    N = {n: var_key("Name", n) for n in names}
    M = {m: var_key("Mother", m) for m in mothers}
    H = {h: var_key("Height", h) for h in heights}

    # Initialize problem
    problem = Problem()

    # Add variables with domains (house positions)
    for var in N.values():
        problem.addVariable(var, houses)
    for var in M.values():
        problem.addVariable(var, houses)
    for var in H.values():
        problem.addVariable(var, houses)

    # Uniqueness constraints for each category
    problem.addConstraint(AllDifferentConstraint(), list(N.values()))
    problem.addConstraint(AllDifferentConstraint(), list(M.values()))
    problem.addConstraint(AllDifferentConstraint(), list(H.values()))

    # Clues as constraints
    # 1. Alice is The person whose mother's name is Aniya.
    problem.addConstraint(lambda a, m: a == m, (N["Alice"], M["Aniya"]))

    # 2. The person who has an average height is somewhere to the left of The person whose mother's name is Penny.
    problem.addConstraint(lambda avg, pen: avg < pen, (H["average"], M["Penny"]))

    # 3. The person whose mother's name is Janelle is Bob.
    problem.addConstraint(lambda j, b: j == b, (M["Janelle"], N["Bob"]))

    # 4. Peter is not in the second house.
    problem.addConstraint(lambda p: p != 2, (N["Peter"],))

    # 5. The person who is short is directly left of Arnold.
    problem.addConstraint(lambda sh, ar: sh == ar - 1, (H["short"], N["Arnold"]))

    # 6. The person who is very tall is Arnold.
    problem.addConstraint(lambda vt, ar: vt == ar, (H["very tall"], N["Arnold"]))

    # 7. Bob is directly left of the person who has an average height.
    problem.addConstraint(lambda b, avg: b == avg - 1, (N["Bob"], H["average"]))

    # 8. Eric is not in the fifth house.
    problem.addConstraint(lambda e: e != 5, (N["Eric"],))

    # 9. The person who is very tall is somewhere to the right of The person whose mother's name is Holly.
    problem.addConstraint(lambda vt, hol: vt > hol, (H["very tall"], M["Holly"]))

    # 10. Eric is The person whose mother's name is Kailyn.
    problem.addConstraint(lambda e, k: e == k, (N["Eric"], M["Kailyn"]))

    # 11. The person who is very short is in the fifth house.
    problem.addConstraint(lambda vs: vs == 5, (H["very short"],))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    # Assume unique solution; take the first
    sol = solutions[0]

    # Build reverse lookups: house -> attribute value
    name_by_house = {}
    for name, var in N.items():
        name_by_house[sol[var]] = name

    mother_by_house = {}
    for mother, var in M.items():
        mother_by_house[sol[var]] = mother

    height_by_house = {}
    for height, var in H.items():
        height_by_house[sol[var]] = height

    # Prepare JSON output
    rows = []
    for h in range(1, 6):
        rows.append([str(h), name_by_house[h], mother_by_house[h], height_by_house[h]])

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()