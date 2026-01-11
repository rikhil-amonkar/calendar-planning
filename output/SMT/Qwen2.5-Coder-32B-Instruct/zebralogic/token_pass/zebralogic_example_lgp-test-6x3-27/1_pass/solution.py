from z3 import *

# Define the domain of each variable
names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
car_models = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

# Create the solver instance
solver = Solver()

# Define variables for each house
name_vars = [Int(f"name_{i}") for i in range(6)]
occupation_vars = [Int(f"occupation_{i}") for i in range(6)]
car_model_vars = [Int(f"car_model_{i}") for i in range(6)]

# Add constraints for each variable to be in the domain
for var in name_vars + occupation_vars + car_model_vars:
    solver.add(var >= 0, var <= 5)

# Unique constraints for each category
solver.add(Distinct(name_vars))
solver.add(Distinct(occupation_vars))
solver.add(Distinct(car_model_vars))

# Map indices to names, occupations, and car models
alice, arnold, eric, peter, bob, carol = 0, 1, 2, 3, 4, 5
engineer, artist, doctor, teacher, nurse, lawyer = 0, 1, 2, 3, 4, 5
chevrolet_silverado, ford_f150, honda_civic, toyota_camry, bmw_3_series, tesla_model_3 = 0, 1, 2, 3, 4, 5

# Clue 1
solver.add(car_model_vars[4] == ford_f150)

# Clue 2
solver.add(car_model_vars[1] != chevrolet_silverado)

# Clue 3
clue3_constraints = []
for i in range(5):
    clue3_constraints.append(Or(And(car_model_vars[i] == honda_civic, name_vars[i+1] == peter),
                               And(car_model_vars[i+1] == honda_civic, name_vars[i] == peter)))
solver.add(Or(clue3_constraints))

# Clue 4
solver.add(occupation_vars[4] != lawyer)

# Clue 5
clue5_constraints = []
for i in range(5):
    clue5_constraints.append(And(occupation_vars[i] == nurse, occupation_vars[i+1] == artist))
solver.add(Or(clue5_constraints))

# Clue 6
clue6_constraints = []
for i in range(6):
    for j in range(i+1, 6):
        clue6_constraints.append(Implies(name_vars[i] == eric, name_vars[j] == carol))
solver.add(And(clue6_constraints))

# Clue 7
solver.add(occupation_vars[eric] == doctor)

# Clue 8
clue8_constraints = []
for i in range(6):
    for j in range(i+1, 6):
        clue8_constraints.append(Implies(occupation_vars[i] == teacher, occupation_vars[j] == nurse))
solver.add(Or(clue8_constraints))

# Clue 9
solver.add(name_vars[5] != carol)

# Clue 10
solver.add(occupation_vars[bob] == engineer)

# Clue 11
clue11_constraints = []
for i in range(6):
    clue11_constraints.append(Implies(car_model_vars[i] == toyota_camry, occupation_vars[i] == nurse))
solver.add(And(clue11_constraints))

# Clue 12
clue12_constraints = []
for i in range(4):
    clue12_constraints.append(Or(And(name_vars[i] == peter, occupation_vars[i+2] == lawyer),
                                And(name_vars[i+2] == peter, occupation_vars[i] == lawyer)))
solver.add(Or(clue12_constraints))

# Clue 13
clue13_constraints = []
for i in range(4):
    clue13_constraints.append(Or(And(car_model_vars[i] == tesla_model_3, name_vars[i+2] == bob),
                                And(car_model_vars[i+2] == tesla_model_3, name_vars[i] == bob)))
solver.add(Or(clue13_constraints))

# Clue 14
solver.add(occupation_vars[arnold] == artist)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "CarModel"],
            "rows": []
        }
    }
    for i in range(6):
        house = str(i + 1)
        name = names[model[name_vars[i]].as_long()]
        occupation = occupations[model[occupation_vars[i]].as_long()]
        car_model = car_models[model[car_model_vars[i]].as_long()]
        solution["solution"]["rows"].append([house, name, occupation, car_model])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")