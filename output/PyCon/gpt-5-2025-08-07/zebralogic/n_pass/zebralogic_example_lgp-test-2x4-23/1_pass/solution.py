import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Houses (positions from left to right)
    houses = [1, 2]

    # Attributes
    Names = ["Eric", "Arnold"]
    Mothers = ["Aniya", "Holly"]
    CarModels = ["ford f150", "tesla model 3"]
    Heights = ["short", "very short"]

    # Helper to build variable names
    def var(category, value):
        return f"{category}:{value}"

    # Set up problem
    problem = Problem()

    # Add variables for each attribute value with domain as possible house positions
    for name in Names:
        problem.addVariable(var("Name", name), houses)
    for mother in Mothers:
        problem.addVariable(var("Mother", mother), houses)
    for car in CarModels:
        problem.addVariable(var("CarModel", car), houses)
    for height in Heights:
        problem.addVariable(var("Height", height), houses)

    # Uniqueness constraints per category
    problem.addConstraint(AllDifferentConstraint(), [var("Name", n) for n in Names])
    problem.addConstraint(AllDifferentConstraint(), [var("Mother", m) for m in Mothers])
    problem.addConstraint(AllDifferentConstraint(), [var("CarModel", c) for c in CarModels])
    problem.addConstraint(AllDifferentConstraint(), [var("Height", h) for h in Heights])

    # Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
    problem.addConstraint(
        lambda arn_pos, tesla_pos: tesla_pos > arn_pos,
        [var("Name", "Arnold"), var("CarModel", "tesla model 3")]
    )

    # Clue 2: Arnold is the person who is short.
    problem.addConstraint(
        lambda arn_pos, short_pos: arn_pos == short_pos,
        [var("Name", "Arnold"), var("Height", "short")]
    )

    # Clue 3: The person whose mother's name is Holly is in the second house.
    problem.addConstraint(
        lambda holly_pos: holly_pos == 2,
        [var("Mother", "Holly")]
    )

    solutions = problem.getSolutions()
    if not solutions:
        output = {
            "solution": {
                "header": ["House", "Name", "Mother", "CarModel", "Height"],
                "rows": []
            }
        }
        print(json.dumps(output, ensure_ascii=False))
        return

    sol = solutions[0]

    # Build rows for houses 1..2
    rows = []
    for house in houses:
        name = next(n for n in Names if sol[var("Name", n)] == house)
        mother = next(m for m in Mothers if sol[var("Mother", m)] == house)
        car = next(c for c in CarModels if sol[var("CarModel", c)] == house)
        height = next(h for h in Heights if sol[var("Height", h)] == house)
        rows.append([str(house), name, mother, car, height])

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()