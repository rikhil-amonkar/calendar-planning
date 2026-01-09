import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define houses and attributes
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]

    # Initialize problem
    problem = Problem()

    # Add variables for each attribute category with domains as house positions
    for n in names:
        problem.addVariable(f"Name_{n}", houses)
    for v in vacations:
        problem.addVariable(f"Vacation_{v}", houses)

    # Each attribute within its category must be assigned to a unique house
    problem.addConstraint(AllDifferentConstraint(), [f"Name_{n}" for n in names])
    problem.addConstraint(AllDifferentConstraint(), [f"Vacation_{v}" for v in vacations])

    # Clue 1: Arnold is somewhere to the right of the person who loves beach vacations.
    problem.addConstraint(
        lambda arnold_pos, beach_pos: arnold_pos > beach_pos,
        ("Name_Arnold", "Vacation_beach")
    )

    # Compute solutions
    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given constraints.")
    # Expecting a unique solution for this puzzle
    sol = solutions[0]

    # Map house positions to attribute values
    pos_to_name = {sol[f"Name_{n}"]: n for n in names}
    pos_to_vac = {sol[f"Vacation_{v}"]: v for v in vacations}

    # Prepare rows ordered by house number
    rows = []
    for h in sorted(houses):
        rows.append([str(h), pos_to_name[h], pos_to_vac[h]])

    # Build final JSON structure
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    output = solve_puzzle()
    print(json.dumps(output, ensure_ascii=False))