from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    solver = Solver()

    # Define the houses
    houses = [1, 2]

    # Define the variables for each attribute
    name = {house: String(f"name_{house}") for house in houses}
    food = {house: String(f"food_{house}") for house in houses}
    mother = {house: String(f"mother_{house}") for house in houses}

    # Possible values for each attribute
    names = ["Arnold", "Eric"]
    foods = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]

    # Add constraints for uniqueness in each attribute across houses
    solver.add(Distinct([name[house] for house in houses]))
    solver.add(Distinct([food[house] for house in houses]))
    solver.add(Distinct([mother[house] for house in houses]))

    # Each attribute must be one of the allowed values
    for house in houses:
        solver.add(Or([name[house] == n for n in names]))
        solver.add(Or([food[house] == f for f in foods]))
        solver.add(Or([mother[house] == m for m in mothers]))

    # Clue 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
    solver.add(Or(
        And(food[1] == "grilled cheese", food[2] == "pizza")
    ))

    # Clue 2: Arnold is not in the second house.
    solver.add(name[2] != "Arnold")

    # Clue 3: Arnold is the person whose mother's name is Holly.
    for house in houses:
        solver.add(Implies(name[house] == "Arnold", mother[house] == "Holly"))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Mother"],
                "rows": []
            }
        }
        for house in sorted(houses):
            row = [
                str(house),
                model.evaluate(name[house]).as_string(),
                model.evaluate(food[house]).as_string(),
                model.evaluate(mother[house]).as_string()
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Food", "Mother"], "rows": []}}

# Generate the solution
solution = solve_scheduling_problem()

# Print the solution in JSON format
import json
print(json.dumps(solution, indent=2))