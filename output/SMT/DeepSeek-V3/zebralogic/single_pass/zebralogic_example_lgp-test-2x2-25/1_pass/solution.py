import json
from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    solver = Solver()

    # Define the houses
    houses = [1, 2]

    # Define the possible names and vacation preferences
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]

    # Create variables for each house's name and vacation
    name_vars = {house: Int(f"name_{house}") for house in houses}
    vacation_vars = {house: Int(f"vacation_{house}") for house in houses}

    # Add constraints that each name and vacation is unique and within valid options
    for house in houses:
        solver.add(Or([name_vars[house] == idx for idx, name in enumerate(names)]))
        solver.add(Or([vacation_vars[house] == idx for idx, vac in enumerate(vacations)]))

    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([vacation_vars[house] for house in houses]))

    # Clue 1: Arnold is somewhere to the right of the person who loves beach vacations.
    # This means the beach lover is to the left of Arnold.
    # So, if beach is in house 1, Arnold must be in house 2.
    # If beach is in house 2, Arnold must be to its right, but there is no house to the right, so this is impossible.
    # Therefore, beach must be in house 1, and Arnold in house 2.
    solver.add(vacation_vars[1] == vacations.index("beach"))
    solver.add(name_vars[2] == names.index("Arnold"))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": []
            }
        }
        for house in sorted(houses):
            name_idx = model.evaluate(name_vars[house]).as_long()
            vacation_idx = model.evaluate(vacation_vars[house]).as_long()
            solution["solution"]["rows"].append([
                str(house),
                names[name_idx],
                vacations[vacation_idx]
            ])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Vacation"], "rows": []}}

# Solve the problem and print the JSON output
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))