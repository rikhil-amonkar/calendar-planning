import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define attributes
    houses = [1, 2, 3]
    names = ["Eric", "Peter", "Arnold"]
    mothers = ["Holly", "Aniya", "Janelle"]
    foods = ["pizza", "grilled cheese", "spaghetti"]

    # Initialize problem
    problem = Problem()

    # Add variables: each attribute value maps to a house number
    for v in names + mothers + foods:
        problem.addVariable(v, houses)

    # Uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), mothers)
    problem.addConstraint(AllDifferentConstraint(), foods)

    # Clue 2: The grilled cheese eater is directly left of Aniya
    problem.addConstraint(lambda gc, an: gc + 1 == an, ("grilled cheese", "Aniya"))

    # Clue 3: The grilled cheese eater is Eric
    problem.addConstraint(lambda eric, gc: eric == gc, ("Eric", "grilled cheese"))

    # Clue 4: Peter's mother is Holly
    problem.addConstraint(lambda peter, holly: peter == holly, ("Peter", "Holly"))

    # Clue 1: The spaghetti eater and Peter are next to each other
    problem.addConstraint(lambda spa, peter: abs(spa - peter) == 1, ("spaghetti", "Peter"))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    solution = solutions[0]

    # Build rows for houses 1..3
    rows = []
    for h in houses:
        name_at_h = next(n for n in names if solution[n] == h)
        mother_at_h = next(m for m in mothers if solution[m] == h)
        food_at_h = next(f for f in foods if solution[f] == h)
        rows.append([str(h), name_at_h, mother_at_h, food_at_h])

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))