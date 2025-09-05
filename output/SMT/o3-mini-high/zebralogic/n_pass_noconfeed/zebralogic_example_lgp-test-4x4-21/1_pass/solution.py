import json
from z3 import *

def main():
    solver = Solver()

    # Define integer variables for each attribute (each in {1,2,3,4})
    # Names
    Eric = Int('Eric')
    Peter = Int('Peter')
    Alice = Int('Alice')
    Arnold = Int('Arnold')

    # Car Models
    tesla_model_3 = Int('tesla_model_3')
    honda_civic = Int('honda_civic')
    toyota_camry = Int('toyota_camry')
    ford_f150 = Int('ford_f150')

    # Birthdays
    jan = Int('jan')
    april = Int('april')
    sept = Int('sept')
    feb = Int('feb')

    # Hobbies
    painting = Int('painting')
    cooking = Int('cooking')
    gardening = Int('gardening')
    photography = Int('photography')

    # List of all variables
    all_vars = [Eric, Peter, Alice, Arnold,
                tesla_model_3, honda_civic, toyota_camry, ford_f150,
                jan, april, sept, feb,
                painting, cooking, gardening, photography]

    # Add domain constraints: each variable must be in {1,2,3,4}
    for var in all_vars:
        solver.add(And(var >= 1, var <= 4))

    # Add distinctness constraints within each category
    solver.add(Distinct(Eric, Peter, Alice, Arnold))
    solver.add(Distinct(tesla_model_3, honda_civic, toyota_camry, ford_f150))
    solver.add(Distinct(jan, april, sept, feb))
    solver.add(Distinct(painting, cooking, gardening, photography))

    # Puzzle Clues translated to constraints:
    # 1. The person whose birthday is in January is not in the second house.
    solver.add(jan != 2)

    # 2. The photography enthusiast is somewhere to the left of Eric.
    solver.add(photography < Eric)

    # 3. The photography enthusiast is somewhere to the left of Peter.
    solver.add(photography < Peter)

    # 4. The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
    solver.add(honda_civic + 1 == tesla_model_3)

    # 5. There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
    solver.add(Or(tesla_model_3 - gardening == 2, gardening - tesla_model_3 == 2))

    # 6. The person who owns a Tesla Model 3 is Arnold.
    solver.add(tesla_model_3 == Arnold)

    # 7. The person whose birthday is in February is the person who loves cooking.
    solver.add(feb == cooking)

    # 8. The person who owns a Toyota Camry is Peter.
    solver.add(toyota_camry == Peter)

    # 9. The person whose birthday is in April is Arnold.
    solver.add(april == Arnold)

    # 10. Alice is the photography enthusiast.
    solver.add(Alice == photography)

    # 11. Peter is the person whose birthday is in January.
    solver.add(Peter == jan)

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        # Extract the model values for each category.
        names = {
            "Eric": model[Eric].as_long(),
            "Peter": model[Peter].as_long(),
            "Alice": model[Alice].as_long(),
            "Arnold": model[Arnold].as_long()
        }
        cars = {
            "tesla model 3": model[tesla_model_3].as_long(),
            "honda civic": model[honda_civic].as_long(),
            "toyota camry": model[toyota_camry].as_long(),
            "ford f150": model[ford_f150].as_long()
        }
        birthdays = {
            "jan": model[jan].as_long(),
            "april": model[april].as_long(),
            "sept": model[sept].as_long(),
            "feb": model[feb].as_long()
        }
        hobbies = {
            "painting": model[painting].as_long(),
            "cooking": model[cooking].as_long(),
            "gardening": model[gardening].as_long(),
            "photography": model[photography].as_long()
        }

        # Build house mapping (houses 1 to 4)
        houses = {h: {"Name": None, "CarModel": None, "Birthday": None, "Hobby": None} for h in range(1, 5)}

        for name, pos in names.items():
            houses[pos]["Name"] = name
        for car, pos in cars.items():
            houses[pos]["CarModel"] = car
        for bday, pos in birthdays.items():
            houses[pos]["Birthday"] = bday
        for hobby, pos in hobbies.items():
            houses[pos]["Hobby"] = hobby

        # Prepare the JSON output in the requested format.
        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                "rows": []
            }
        }

        # Ensure rows are in house order (1,2,3,4)
        for h in range(1, 5):
            row = [
                str(h),
                houses[h]["Name"],
                houses[h]["CarModel"],
                houses[h]["Birthday"],
                houses[h]["Hobby"]
            ]
            solution["solution"]["rows"].append(row)

        print(json.dumps(solution, indent=2))
    else:
        # In case no solution is found.
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()