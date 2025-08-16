from z3 import *
import json

def solve_scheduling_problem():
    # Create a solver instance
    solver = Solver()

    # Define the houses
    houses = [1, 2]

    # Define variables for each attribute in each house
    name = {house: String(f"name_{house}") for house in houses}
    mother = {house: String(f"mother_{house}") for house in houses}
    car_model = {house: String(f"car_model_{house}") for house in houses}
    height = {house: String(f"height_{house}") for house in houses}

    # Possible values for each attribute
    names = ["Eric", "Arnold"]
    mothers = ["Aniya", "Holly"]
    car_models = ["ford f150", "tesla model 3"]
    heights = ["short", "very short"]

    # Add constraints for each house
    for house in houses:
        solver.add(Or([name[house] == n for n in names]))
        solver.add(Or([mother[house] == m for m in mothers]))
        solver.add(Or([car_model[house] == c for c in car_models]))
        solver.add(Or([height[house] == h for h in heights]))

    # Add uniqueness constraints across houses
    for attr in [name, mother, car_model, height]:
        solver.add(Distinct([attr[house] for house in houses]))

    # Apply the clues
    # Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
    # This means Arnold is in a house with a lower number than the Tesla owner.
    for house in houses:
        for other_house in houses:
            if other_house > house:
                solver.add(Implies(name[house] == "Arnold", car_model[other_house] == "tesla model 3"))

    # Clue 2: Arnold is the person who is short.
    for house in houses:
        solver.add(Implies(name[house] == "Arnold", height[house] == "short"))

    # Clue 3: The person whose mother's name is Holly is in the second house.
    solver.add(mother[2] == "Holly")

    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "CarModel", "Height"],
                "rows": []
            }
        }
        for house in sorted(houses):
            row = [
                str(house),
                model.eval(name[house]).as_string(),
                model.eval(mother[house]).as_string(),
                model.eval(car_model[house]).as_string(),
                model.eval(height[house]).as_string()
            ]
            solution["solution"]["rows"].append(row)
        return json.dumps(solution, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

# Print the solution
print(solve_scheduling_problem())