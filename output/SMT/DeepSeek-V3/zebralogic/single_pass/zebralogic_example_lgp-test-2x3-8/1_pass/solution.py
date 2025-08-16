from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    solver = Solver()

    # Define the houses
    houses = [1, 2]

    # Define the attributes
    names = ["Arnold", "Eric"]
    birthdays = ["april", "sept"]
    mothers = ["Aniya", "Holly"]

    # Create variables for each attribute in each house
    name_vars = {house: String(f"name_{house}") for house in houses}
    birthday_vars = {house: String(f"birthday_{house}") for house in houses}
    mother_vars = {house: String(f"mother_{house}") for house in houses}

    # Add constraints for uniqueness of each attribute
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([birthday_vars[house] for house in houses]))
    solver.add(Distinct([mother_vars[house] for house in houses]))

    # Each attribute must be one of the allowed values
    for house in houses:
        solver.add(Or([name_vars[house] == name for name in names]))
        solver.add(Or([birthday_vars[house] == bday for bday in birthdays]))
        solver.add(Or([mother_vars[house] == mother for mother in mothers]))

    # Apply clue 1: Eric is to the left of the person whose mother's name is Holly
    # This means if Eric is in house 1, mother in house 2 is Holly, or Eric is not in house 2
    solver.add(Or(
        And(name_vars[1] == "Eric", mother_vars[2] == "Holly"),
        And(name_vars[2] == "Eric", False)  # This can never be true, so it's effectively only the first case
    ))

    # Apply clue 2: The person whose birthday is in April is in the first house
    solver.add(birthday_vars[1] == "april")

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother"],
                "rows": []
            }
        }
        for house in sorted(houses):
            name = model.evaluate(name_vars[house]).as_string()
            birthday = model.evaluate(birthday_vars[house]).as_string()
            mother = model.evaluate(mother_vars[house]).as_string()
            solution["solution"]["rows"].append([str(house), name, birthday, mother])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Birthday", "Mother"], "rows": []}}

# Generate the solution
solution = solve_scheduling_problem()
print(solution)