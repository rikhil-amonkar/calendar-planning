from z3 import *
import json

def main():
    solver = Solver()

    # There are 6 houses, indexed 0 to 5 (House number = index+1)
    houses = list(range(6))
    
    # Define arrays for each attribute
    names = [Int("name_%d" % i) for i in houses]
    cars = [Int("car_%d" % i) for i in houses]
    mothers = [Int("mother_%d" % i) for i in houses]
    hobbies = [Int("hobby_%d" % i) for i in houses]

    # Domain constraints: each variable is between 0 and 5
    for i in houses:
        solver.add(names[i] >= 0, names[i] < 6)
        solver.add(cars[i] >= 0, cars[i] < 6)
        solver.add(mothers[i] >= 0, mothers[i] < 6)
        solver.add(hobbies[i] >= 0, hobbies[i] < 6)

    # All attributes are a permutation over the 6 houses.
    solver.add(Distinct(names))
    solver.add(Distinct(cars))
    solver.add(Distinct(mothers))
    solver.add(Distinct(hobbies))

    # Define our mappings:
    # Names: Eric=0, Bob=1, Peter=2, Alice=3, Arnold=4, Carol=5.
    # Cars: ford f150=0, honda civic=1, toyota camry=2, tesla model 3=3, chevrolet silverado=4, bmw 3 series=5.
    # Mothers: Sarah=0, Penny=1, Holly=2, Aniya=3, Kailyn=4, Janelle=5.
    # Hobbies: photography=0, cooking=1, knitting=2, gardening=3, woodworking=4, painting=5.

    # Constraint 1: The person who owns a Toyota Camry is in the sixth house.
    solver.add(cars[5] == 2)

    # Constraint 2: Carol is the photography enthusiast.
    for i in houses:
        solver.add(Implies(names[i] == 5, hobbies[i] == 0))

    # Constraint 3: The person who owns a Chevrolet Silverado is the person whose mother's name is Aniya.
    for i in houses:
        solver.add(Or(And(cars[i] == 4, mothers[i] == 3),
                        And(cars[i] != 4, mothers[i] != 3)))

    # Constraint 4: The person who owns a Chevrolet Silverado is not in the second house.
    solver.add(cars[1] != 4)

    # Constraint 5: The person who owns a Ford F-150 is the person whose mother's name is Sarah.
    for i in houses:
        solver.add(Or(And(cars[i] == 0, mothers[i] == 0),
                        And(cars[i] != 0, mothers[i] != 0)))

    # Constraint 6: The person who owns a BMW 3 Series is Bob.
    for i in houses:
        solver.add(Or(And(cars[i] == 5, names[i] == 1),
                        And(cars[i] != 5, names[i] != 1)))

    # Constraint 7: The person whose mother's name is Kailyn is in the sixth house.
    solver.add(mothers[5] == 4)

    # Constraint 8: Eric is directly left of the person who enjoys knitting.
    # For houses 0 to 4, if a house is Eric then the next house must have knitting.
    for i in range(5):
        solver.add(Implies(names[i] == 0, hobbies[i+1] == 2))
    # Also, Eric cannot be in the last house.
    solver.add(Implies(names[5] == 0, False))

    # Constraint 9: There is one house between the person whose mother's name is Sarah and the person who owns a Toyota Camry.
    # Since Toyota Camry is in house 6 (index 5), Sarah must be in house 4 (index 3).
    solver.add(mothers[3] == 0)

    # Constraint 10: The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
    for i in houses:
        for j in houses:
            # If house i has knitting and house j has Penny, then i must be to the left of j.
            solver.add(Implies(And(hobbies[i] == 2, mothers[j] == 1), i < j))

    # Constraint 11: The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
    for i in houses:
        for j in houses:
            # If house i has Aniya and house j has Honda Civic, then j must be to the left of i.
            solver.add(Implies(And(mothers[i] == 3, cars[j] == 1), j < i))

    # Constraint 12: Alice is somewhere to the right of the person who owns a Ford F-150.
    for i in houses:
        for j in houses:
            # If house i is Alice and house j has a Ford F-150, then j must be to the left of i.
            solver.add(Implies(And(names[i] == 3, cars[j] == 0), j < i))

    # Constraint 13: Eric is the person who enjoys gardening.
    for i in houses:
        solver.add(Implies(names[i] == 0, hobbies[i] == 3))

    # Constraint 14: The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(hobbies[i] == 4, hobbies[j] == 2), i < j))

    # Constraint 15: There is one house between the person whose mother's name is Sarah and the person who loves cooking.
    # Since Sarah is in house 4 (index 3), cooking must be in house 2 (index 1) or house 6 (index 5).
    for i in houses:
        solver.add(Implies(hobbies[i] == 1, Or(i == 1, i == 5)))

    # Constraint 16: The person who owns a Honda Civic is Arnold.
    for i in houses:
        solver.add(Or(And(cars[i] == 1, names[i] == 4),
                        And(cars[i] != 1, names[i] != 4)))

    # Constraint 17: The person whose mother's name is Holly is directly left of the person who enjoys knitting.
    for i in range(5):
        solver.add(Implies(mothers[i] == 2, hobbies[i+1] == 2))
    # Ensure Holly is not in the last house.
    solver.add(Implies(mothers[5] == 2, False))

    # Solve and output the results in the required JSON format.
    if solver.check() == sat:
        model = solver.model()
        # Reverse mapping lists to output the actual attribute names.
        name_list = ["Eric", "Bob", "Peter", "Alice", "Arnold", "Carol"]
        car_list = ["ford f150", "honda civic", "toyota camry", "tesla model 3", "chevrolet silverado", "bmw 3 series"]
        mother_list = ["Sarah", "Penny", "Holly", "Aniya", "Kailyn", "Janelle"]
        hobby_list = ["photography", "cooking", "knitting", "gardening", "woodworking", "painting"]

        rows = []
        for i in houses:
            row = [
                str(i+1),
                name_list[model.evaluate(names[i]).as_long()],
                car_list[model.evaluate(cars[i]).as_long()],
                mother_list[model.evaluate(mothers[i]).as_long()],
                hobby_list[model.evaluate(hobbies[i]).as_long()]
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()