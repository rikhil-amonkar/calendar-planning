from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    solver = Solver()

    # Define the houses
    houses = [1, 2, 3]

    # Define the attributes
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]

    # Create variables for each attribute in each house
    name_vars = {house: String(f"name_{house}") for house in houses}
    education_vars = {house: String(f"education_{house}") for house in houses}
    occupation_vars = {house: String(f"occupation_{house}") for house in houses}

    # Add constraints for uniqueness of each attribute
    for house in houses:
        solver.add(Or([name_vars[house] == name for name in names]))
        solver.add(Or([education_vars[house] == edu for edu in educations]))
        solver.add(Or([occupation_vars[house] == occ for occ in occupations]))

    # All names, educations, and occupations must be distinct
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([education_vars[house] for house in houses]))
    solver.add(Distinct([occupation_vars[house] for house in houses]))

    # Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
    # This means the teacher is in house X, and associate is in house X+1.
    for i in range(1, 3):
        solver.add(Implies(occupation_vars[i] == "teacher", education_vars[i+1] == "associate"))

    # Clue 2: The person with an associate's degree and Eric are next to each other.
    # This means if associate is in X, Eric is in X-1 or X+1, and vice versa.
    for i in houses:
        for j in houses:
            if abs(i - j) == 1:
                solver.add(Implies(education_vars[i] == "associate", name_vars[j] == "Eric"))
                solver.add(Implies(name_vars[i] == "Eric", education_vars[j] == "associate"))

    # Clue 3: Peter is the person with a high school diploma.
    for house in houses:
        solver.add(Implies(name_vars[house] == "Peter", education_vars[house] == "high school"))

    # Clue 4: The person who is a doctor is the person with a bachelor's degree.
    for house in houses:
        solver.add(Implies(occupation_vars[house] == "doctor", education_vars[house] == "bachelor"))

    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Education", "Occupation"],
                "rows": []
            }
        }
        for house in sorted(houses):
            name = model.eval(name_vars[house])
            education = model.eval(education_vars[house])
            occupation = model.eval(occupation_vars[house])
            solution["solution"]["rows"].append([str(house), str(name), str(education), str(occupation)])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Education", "Occupation"], "rows": []}}

# Print the solution as JSON
import json
print(json.dumps(solve_scheduling_problem(), indent=2))