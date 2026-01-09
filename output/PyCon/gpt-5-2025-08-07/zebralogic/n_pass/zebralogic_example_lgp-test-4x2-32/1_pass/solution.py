import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]

    problem = Problem()

    # Variables: positions of each person and pet (house numbers)
    problem.addVariables(names, houses)
    problem.addVariables(pets, houses)

    # All different constraints within categories
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), pets)

    # Clue constraints:
    # 1. The person who owns a dog is somewhere to the right of Alice.
    problem.addConstraint(lambda dog, Alice: dog > Alice, ("dog", "Alice"))

    # 2. Eric is not in the first house.
    problem.addConstraint(lambda Eric: Eric != 1, ("Eric",))

    # 3. Eric is the person who keeps a pet bird.
    problem.addConstraint(lambda Eric, bird: Eric == bird, ("Eric", "bird"))

    # 4. There is one house between the person with an aquarium of fish and Peter.
    problem.addConstraint(lambda fish, Peter: abs(fish - Peter) == 2, ("fish", "Peter"))

    # 5. Alice is not in the first house.
    problem.addConstraint(lambda Alice: Alice != 1, ("Alice",))

    # 6. Arnold is the person with an aquarium of fish.
    problem.addConstraint(lambda Arnold, fish: Arnold == fish, ("Arnold", "fish"))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the puzzle constraints.")

    solution = solutions[0]

    # Build house-wise rows
    name_by_house = {solution[name]: name for name in names}
    pet_by_house = {solution[pet]: pet for pet in pets}

    rows = []
    for h in sorted(houses):
        rows.append([str(h), name_by_house[h], pet_by_house[h]])

    output = {
        "solution": {
            "header": ["House", "Name", "Pet"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))