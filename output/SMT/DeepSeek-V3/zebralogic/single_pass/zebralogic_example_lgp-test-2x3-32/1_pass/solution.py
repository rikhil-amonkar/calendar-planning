import json
from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    solver = Solver()

    # Define the houses
    houses = [1, 2]

    # Define variables for each attribute
    names = {house: String(f"name_{house}") for house in houses}
    birthdays = {house: String(f"birthday_{house}") for house in houses}
    colors = {house: String(f"color_{house}") for house in houses}

    # Possible values for each attribute
    possible_names = ["Eric", "Arnold"]
    possible_birthdays = ["sept", "april"]
    possible_colors = ["yellow", "red"]

    # Add constraints for uniqueness and possible values
    for house in houses:
        solver.add(Or([names[house] == name for name in possible_names]))
        solver.add(Or([birthdays[house] == bday for bday in possible_birthdays]))
        solver.add(Or([colors[house] == color for color in possible_colors]))

    # Ensure all names, birthdays, and colors are unique
    solver.add(Distinct([names[house] for house in houses]))
    solver.add(Distinct([birthdays[house] for house in houses]))
    solver.add(Distinct([colors[house] for house in houses]))

    # Apply the given clues
    # Clue 1: Eric loves yellow
    solver.add(Exists([house for house in houses], And(names[house] == "Eric", colors[house] == "yellow")))

    # Clue 2: The person whose birthday is in April is in the first house
    solver.add(birthdays[1] == "april")

    # Clue 3: The person who loves yellow is not in the first house
    solver.add(colors[1] != "yellow")

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Color"],
                "rows": []
            }
        }
        for house in sorted(houses):
            name = model.evaluate(names[house])
            birthday = model.evaluate(birthdays[house])
            color = model.evaluate(colors[house])
            solution["solution"]["rows"].append([
                str(house),
                str(name),
                str(birthday),
                str(color)
            ])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Birthday", "Color"], "rows": []}}

# Get the solution and print it as JSON
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))