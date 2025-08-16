import json
from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    solver = Solver()

    # Define the houses
    houses = [1, 2]

    # Define the possible values for each attribute
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]

    # Create variables for each attribute in each house
    name_vars = {house: String(f"name_{house}") for house in houses}
    sport_vars = {house: String(f"sport_{house}") for house in houses}
    hobby_vars = {house: String(f"hobby_{house}") for house in houses}

    # Add constraints that each attribute must be one of the allowed values
    for house in houses:
        solver.add(Or([name_vars[house] == name for name in names]))
        solver.add(Or([sport_vars[house] == sport for sport in sports]))
        solver.add(Or([hobby_vars[house] == hobby for hobby in hobbies]))

    # Add uniqueness constraints for each attribute across houses
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([sport_vars[house] for house in houses]))
    solver.add(Distinct([hobby_vars[house] for house in houses]))

    # Apply the given clues
    # Clue 1: The person who enjoys gardening is Arnold.
    for house in houses:
        solver.add(Implies(hobby_vars[house] == "gardening", name_vars[house] == "Arnold"))

    # Clue 2: The photography enthusiast is not in the first house.
    solver.add(hobby_vars[1] != "photography")

    # Clue 3: The person who loves soccer is not in the first house.
    solver.add(sport_vars[1] != "soccer")

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        # Prepare the solution in the required format
        solution = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "Hobby"],
                "rows": []
            }
        }
        for house in sorted(houses):
            name = model.eval(name_vars[house])
            sport = model.eval(sport_vars[house])
            hobby = model.eval(hobby_vars[house])
            solution["solution"]["rows"].append([
                str(house),
                str(name),
                str(sport),
                str(hobby)
            ])
        return solution
    else:
        return {"error": "No solution found"}

# Get the solution and print it as JSON
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))