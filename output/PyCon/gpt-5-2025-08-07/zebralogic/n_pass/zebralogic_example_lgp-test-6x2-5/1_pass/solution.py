import json
import sys
import subprocess

# Ensure python-constraint is available
try:
    from constraint import Problem, AllDifferentConstraint
except ImportError:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "python-constraint"])
    from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = range(1, 7)
    names = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    problem = Problem()

    # Variables: each Name/Vacation maps to a house number 1..6
    for n in names:
        problem.addVariable(f"N_{n}", houses)
    for v in vacations:
        problem.addVariable(f"V_{v}", houses)

    # Uniqueness constraints
    problem.addConstraint(AllDifferentConstraint(), [f"N_{n}" for n in names])
    problem.addConstraint(AllDifferentConstraint(), [f"V_{v}" for v in vacations])

    # Clues:
    # 1. Cultural is left of Beach
    problem.addConstraint(lambda c, b: c < b, ("V_cultural", "V_beach"))

    # 2. Eric is to the right of Alice
    problem.addConstraint(lambda e, a: e > a, ("N_Eric", "N_Alice"))

    # 3. Eric is in the second house
    problem.addConstraint(lambda e: e == 2, ("N_Eric",))

    # 4. Cultural is in the third house
    problem.addConstraint(lambda c: c == 3, ("V_cultural",))

    # 5. Bob is directly left of Arnold
    problem.addConstraint(lambda b, a: b + 1 == a, ("N_Bob", "N_Arnold"))

    # 6. Camping is not in the first house
    problem.addConstraint(lambda c: c != 1, ("V_camping",))

    # 7. Cultural is Peter
    problem.addConstraint(lambda p, c: p == c, ("N_Peter", "V_cultural"))

    # 8. Cruise is Bob
    problem.addConstraint(lambda vc, nb: vc == nb, ("V_cruise", "N_Bob"))

    # 9. City is in the fourth house
    problem.addConstraint(lambda c: c == 4, ("V_city",))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")

    sol = solutions[0]

    # Build house -> name and house -> vacation mappings
    house_to_name = {sol[f"N_{n}"]: n for n in names}
    house_to_vac = {sol[f"V_{v}"]: v for v in vacations}

    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": []
        }
    }

    for h in range(1, 7):
        result["solution"]["rows"].append([str(h), house_to_name[h], house_to_vac[h]])

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()