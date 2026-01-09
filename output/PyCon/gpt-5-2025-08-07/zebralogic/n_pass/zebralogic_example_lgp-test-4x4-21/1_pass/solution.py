import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()

    houses = [1, 2, 3, 4]

    # Attributes
    names = ["Eric", "Peter", "Alice", "Arnold"]
    cars = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
    months = ["jan", "april", "sept", "feb"]
    hobbies = ["painting", "cooking", "gardening", "photography"]

    # Add variables for each attribute with domain as house numbers
    problem.addVariables(names, houses)
    problem.addVariables(cars, houses)
    problem.addVariables(months, houses)
    problem.addVariables(hobbies, houses)

    # AllDifferent constraints for each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), cars)
    problem.addConstraint(AllDifferentConstraint(), months)
    problem.addConstraint(AllDifferentConstraint(), hobbies)

    # Clues as constraints:

    # 1. The person whose birthday is in January is not in the second house.
    problem.addConstraint(lambda j: j != 2, ("jan",))

    # 2. The photography enthusiast is somewhere to the left of Eric.
    problem.addConstraint(lambda photo, eric: photo < eric, ("photography", "Eric"))

    # 3. The photography enthusiast is somewhere to the left of Peter.
    problem.addConstraint(lambda photo, peter: photo < peter, ("photography", "Peter"))

    # 4. The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
    problem.addConstraint(lambda honda, tesla: honda == tesla - 1, ("honda civic", "tesla model 3"))

    # 5. There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
    problem.addConstraint(lambda tesla, gardening: abs(tesla - gardening) == 2, ("tesla model 3", "gardening"))

    # 6. The person who owns a Tesla Model 3 is Arnold.
    problem.addConstraint(lambda tesla, arnold: tesla == arnold, ("tesla model 3", "Arnold"))

    # 7. The person whose birthday is in February is the person who loves cooking.
    problem.addConstraint(lambda feb, cooking: feb == cooking, ("feb", "cooking"))

    # 8. The person who owns a Toyota Camry is Peter.
    problem.addConstraint(lambda toyota, peter: toyota == peter, ("toyota camry", "Peter"))

    # 9. The person whose birthday is in April is Arnold.
    problem.addConstraint(lambda april, arnold: april == arnold, ("april", "Arnold"))

    # 10. Alice is the photography enthusiast.
    problem.addConstraint(lambda alice, photo: alice == photo, ("Alice", "photography"))

    # 11. Peter is the person whose birthday is in January.
    problem.addConstraint(lambda peter, jan: peter == jan, ("Peter", "jan"))

    solutions = problem.getSolutions()

    if not solutions:
        raise RuntimeError("No solution found")

    sol = solutions[0]

    # Build mapping from house to each attribute
    house_to_name = {sol[name]: name for name in names}
    house_to_car = {sol[car]: car for car in cars}
    house_to_birthday = {sol[month]: month for month in months}
    house_to_hobby = {sol[hobby]: hobby for hobby in hobbies}

    # Prepare JSON structure
    output = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
            "rows": []
        }
    }

    for h in sorted(houses):
        row = [
            str(h),
            house_to_name[h],
            house_to_car[h],
            house_to_birthday[h],
            house_to_hobby[h]
        ]
        output["solution"]["rows"].append(row)

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()