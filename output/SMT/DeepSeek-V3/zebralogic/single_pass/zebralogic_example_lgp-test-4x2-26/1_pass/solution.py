from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4]

    # Define the names and occupations
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]

    # Create variables for each house's name and occupation
    name_vars = {house: String(f"name_{house}") for house in houses}
    occupation_vars = {house: String(f"occupation_{house}") for house in houses}

    # Add constraints that each name and occupation is unique
    s.add(Distinct([name_vars[house] for house in houses]))
    s.add(Distinct([occupation_vars[house] for house in houses]))

    # Each name and occupation must be one of the allowed values
    for house in houses:
        s.add(Or([name_vars[house] == name for name in names]))
        s.add(Or([occupation_vars[house] == occupation for occupation in occupations]))

    # Clue 1: There are two houses between Eric and Peter.
    # This means if Eric is in house X, Peter is in house X+3, or vice versa.
    # Since there are only 4 houses, Eric must be in 1 and Peter in 4, or Eric in 2 and Peter in 5 (invalid), so only Eric in 1 and Peter in 4.
    s.add(Or(
        And(name_vars[1] == "Eric", name_vars[4] == "Peter"),
        And(name_vars[4] == "Eric", name_vars[1] == "Peter")
    ))

    # Clue 2: The person who is a teacher is Peter.
    for house in houses:
        s.add(Implies(occupation_vars[house] == "teacher", name_vars[house] == "Peter"))

    # Clue 3: Peter is not in the first house.
    s.add(name_vars[1] != "Peter")

    # From Clue 1 and Clue 3, Peter must be in house 4, and Eric in house 1.
    s.add(name_vars[1] == "Eric")
    s.add(name_vars[4] == "Peter")

    # Clue 4: There is one house between the person who is a doctor and Alice.
    # This means if doctor is in X, Alice is in X+2, or vice versa.
    # Possible positions:
    # - doctor in 1, Alice in 3
    # - doctor in 2, Alice in 4
    # Or:
    # - Alice in 1, doctor in 3
    # - Alice in 2, doctor in 4
    # But Alice cannot be in 4 because Peter is in 4 (names are unique), so Alice is in 1, 2, or 3.
    s.add(Or(
        And(occupation_vars[1] == "doctor", name_vars[3] == "Alice"),
        And(occupation_vars[2] == "doctor", name_vars[4] == "Alice"),
        And(name_vars[1] == "Alice", occupation_vars[3] == "doctor"),
        And(name_vars[2] == "Alice", occupation_vars[4] == "doctor")
    ))

    # Clue 5: The person who is an artist is Alice.
    for house in houses:
        s.add(Implies(occupation_vars[house] == "artist", name_vars[house] == "Alice"))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation"],
                "rows": []
            }
        }
        for house in houses:
            name = model.eval(name_vars[house])
            occupation = model.eval(occupation_vars[house])
            solution["solution"]["rows"].append([str(house), str(name), str(occupation)])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Occupation"], "rows": []}}

# Solve the problem and print the result
solution = solve_scheduling_problem()
print(solution)