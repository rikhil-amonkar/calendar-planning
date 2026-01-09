import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 7)

    Names = ["Eric", "Bob", "Peter", "Alice", "Arnold", "Carol"]
    CarModels = ["ford f150", "honda civic", "toyota camry", "tesla model 3", "chevrolet silverado", "bmw 3 series"]
    Mothers = ["Sarah", "Penny", "Holly", "Aniya", "Kailyn", "Janelle"]
    Hobbies = ["photography", "cooking", "knitting", "gardening", "woodworking", "painting"]

    problem = Problem()

    # Add variables
    for n in Names:
        problem.addVariable(n, houses)
    for c in CarModels:
        problem.addVariable(c, houses)
    for m in Mothers:
        problem.addVariable(m, houses)
    for h in Hobbies:
        problem.addVariable(h, houses)

    # All different within each category
    problem.addConstraint(AllDifferentConstraint(), Names)
    problem.addConstraint(AllDifferentConstraint(), CarModels)
    problem.addConstraint(AllDifferentConstraint(), Mothers)
    problem.addConstraint(AllDifferentConstraint(), Hobbies)

    # Clues implementation

    # 1. The person who owns a Toyota Camry is in the sixth house.
    problem.addConstraint(lambda x: x == 6, ("toyota camry",))

    # 2. Carol is the photography enthusiast.
    problem.addConstraint(lambda a, b: a == b, ("Carol", "photography"))

    # 3. Chevrolet Silverado owner is the person whose mother's name is Aniya.
    problem.addConstraint(lambda a, b: a == b, ("chevrolet silverado", "Aniya"))

    # 4. The person who owns a Chevrolet Silverado is not in the second house.
    problem.addConstraint(lambda x: x != 2, ("chevrolet silverado",))

    # 5. Ford F-150 owner is the person whose mother's name is Sarah.
    problem.addConstraint(lambda a, b: a == b, ("ford f150", "Sarah"))

    # 6. BMW 3 Series owner is Bob.
    problem.addConstraint(lambda a, b: a == b, ("bmw 3 series", "Bob"))

    # 7. The person whose mother's name is Kailyn is in the sixth house.
    problem.addConstraint(lambda x: x == 6, ("Kailyn",))

    # 8. Eric is directly left of the person who enjoys knitting.
    problem.addConstraint(lambda eric, knit: eric == knit - 1, ("Eric", "knitting"))

    # 9. There is one house between Sarah and the person who owns a Toyota Camry.
    problem.addConstraint(lambda sarah, camry: abs(sarah - camry) == 2, ("Sarah", "toyota camry"))

    # 10. Penny is somewhere to the right of the person who enjoys knitting.
    problem.addConstraint(lambda penny, knit: penny > knit, ("Penny", "knitting"))

    # 11. Aniya is somewhere to the right of the person who owns a Honda Civic.
    problem.addConstraint(lambda aniya, civic: aniya > civic, ("Aniya", "honda civic"))

    # 12. Alice is somewhere to the right of the person who owns a Ford F-150.
    problem.addConstraint(lambda alice, f150: alice > f150, ("Alice", "ford f150"))

    # 13. Eric is the person who enjoys gardening.
    problem.addConstraint(lambda eric, garden: eric == garden, ("Eric", "gardening"))

    # 14. The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    problem.addConstraint(lambda wood, knit: wood < knit, ("woodworking", "knitting"))

    # 15. There is one house between Sarah and the person who loves cooking.
    problem.addConstraint(lambda sarah, cook: abs(sarah - cook) == 2, ("Sarah", "cooking"))

    # 16. The person who owns a Honda Civic is Arnold.
    problem.addConstraint(lambda civic, arnold: civic == arnold, ("honda civic", "Arnold"))

    # 17. The person whose mother's name is Holly is directly left of the person who enjoys knitting.
    problem.addConstraint(lambda holly, knit: holly == knit - 1, ("Holly", "knitting"))

    solutions = problem.getSolutions()
    if not solutions:
        output = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                "rows": []
            }
        }
        print(json.dumps(output))
        return

    sol = solutions[0]

    rows = []
    for house in range(1, 7):
        name = next(n for n in Names if sol[n] == house)
        car = next(c for c in CarModels if sol[c] == house)
        mother = next(m for m in Mothers if sol[m] == house)
        hobby = next(h for h in Hobbies if sol[h] == house)
        rows.append([str(house), name, car, mother, hobby])

    result = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
            "rows": rows
        }
    }

    print(json.dumps(result))

if __name__ == "__main__":
    main()