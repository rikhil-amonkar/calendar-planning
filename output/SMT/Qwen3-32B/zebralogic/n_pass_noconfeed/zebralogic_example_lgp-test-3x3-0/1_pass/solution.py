import json
from z3 import *

def solve_puzzle():
    # Define variables for each house (1, 2, 3) for name, education, occupation
    name = [Int(f'name_{i+1}') for i in range(3)]
    education = [Int(f'education_{i+1}') for i in range(3)]
    occupation = [Int(f'occupation_{i+1}') for i in range(3)]

    solver = Solver()

    # Add distinct constraints for each attribute
    for var_list in [name, education, occupation]:
        solver.add(Distinct(var_list))
        for var in var_list:
            solver.add(And(0 <= var, var <= 2))

    # Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
    clue1 = Or(
        And(occupation[0] == 0, education[1] == 1),
        And(occupation[1] == 0, education[2] == 1)
    )
    solver.add(clue1)

    # Clue 2: The person with an associate's degree and Eric are next to each other.
    clue2 = Or(
        And(education[0] == 1, name[1] == 1),
        And(education[1] == 1, Or(name[0] == 1, name[2] == 1)),
        And(education[2] == 1, name[1] == 1)
    )
    solver.add(clue2)

    # Clue 3: Peter is the person with a high school diploma.
    for i in range(3):
        solver.add(Implies(name[i] == 0, education[i] == 2))

    # Clue 4: The person who is a doctor is the person with a bachelor's degree.
    for i in range(3):
        solver.add(Implies(occupation[i] == 1, education[i] == 0))

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        # Prepare the solution data
        rows = []
        for i in range(3):
            house_num = i + 1
            name_val = model[name[i]].as_long()
            education_val = model[education[i]].as_long()
            occupation_val = model[occupation[i]].as_long()

            name_str = {0: 'Peter', 1: 'Eric', 2: 'Arnold'}[name_val]
            education_str = {0: 'bachelor', 1: 'associate', 2: 'high school'}[education_val]
            occupation_str = {0: 'teacher', 1: 'doctor', 2: 'engineer'}[occupation_val]

            rows.append([str(house_num), name_str, education_str, occupation_str])

        solution = {
            "solution": {
                "header": ["House", "Name", "Education", "Occupation"],
                "rows": rows
            }
        }

        # Output as JSON
        return json.dumps(solution, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

# Run and print the result
print(solve_puzzle())