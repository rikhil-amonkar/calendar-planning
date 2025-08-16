from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the names and vacations
    names = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    # Create variables for each house's name and vacation
    name_vars = {house: String(f"name_{house}") for house in houses}
    vacation_vars = {house: String(f"vacation_{house}") for house in houses}

    # Add constraints for unique names and vacations
    s.add(Distinct([name_vars[house] for house in houses]))
    s.add(Distinct([vacation_vars[house] for house in houses]))

    # Each name and vacation must be one of the allowed values
    for house in houses:
        s.add(Or([name_vars[house] == name for name in names]))
        s.add(Or([vacation_vars[house] == vacation for vacation in vacations]))

    # Clue 3: Eric is in the second house
    s.add(name_vars[2] == "Eric")

    # Clue 2: Eric is somewhere to the right of Alice (Alice is to the left of Eric)
    # Since Eric is in house 2, Alice must be in house 1
    s.add(name_vars[1] == "Alice")

    # Clue 4: The person who goes on cultural tours is in the third house
    s.add(vacation_vars[3] == "cultural")

    # Clue 7: The person who goes on cultural tours is Peter
    s.add(name_vars[3] == "Peter")

    # Clue 5: Bob is directly left of Arnold (Bob is in house X, Arnold in X+1)
    # Possible positions for Bob: 1 to 5, Arnold: 2 to 6
    # But Alice is in 1, Eric in 2, Peter in 3, so Bob can be in 4 or 5
    s.add(Or(
        And(name_vars[4] == "Bob", name_vars[5] == "Arnold"),
        And(name_vars[5] == "Bob", name_vars[6] == "Arnold")
    ))

    # Clue 8: The person who likes going on cruises is Bob
    for house in houses:
        s.add(Implies(name_vars[house] == "Bob", vacation_vars[house] == "cruise"))

    # Clue 9: The person who prefers city breaks is in the fourth house
    s.add(vacation_vars[4] == "city")

    # Clue 1: The person who goes on cultural tours is somewhere to the left of the person who loves beach vacations
    # cultural is in house 3, so beach must be in house 4, 5, or 6
    s.add(Or(
        vacation_vars[4] == "beach",
        vacation_vars[5] == "beach",
        vacation_vars[6] == "beach"
    ))

    # Clue 6: The person who enjoys camping trips is not in the first house
    s.add(vacation_vars[1] != "camping")

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": []
            }
        }
        for house in houses:
            name = model.eval(name_vars[house]).as_string()
            vacation = model.eval(vacation_vars[house]).as_string()
            solution["solution"]["rows"].append([str(house), name, vacation])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Vacation"], "rows": []}}

# Print the solution in JSON format
import json
print(json.dumps(solve_scheduling_problem(), indent=2))