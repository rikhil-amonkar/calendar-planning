from z3 import *

# Define variables
houses = range(1, 7)
names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

# Create dictionaries for each variable type
name_vars = {h: Int(f'name_{h}') for h in houses}
mother_vars = {h: Int(f'mother_{h}') for h in houses}
pet_vars = {h: Int(f'pet_{h}') for h in houses}

# Create solvers
solver = Solver()

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[h] for h in houses]))
solver.add(Distinct([mother_vars[h] for h in houses]))
solver.add(Distinct([pet_vars[h] for h in houses]))

# Map values to integers
name_map = {n: i for i, n in enumerate(names)}
mother_map = {m: i for i, m in enumerate(mothers)}
pet_map = {p: i for i, p in enumerate(pets)}

# Add specific constraints
solver.add(name_vars[3] == name_map["Arnold"])
solver.add(mother_vars[3] == mother_map["Janelle"])
solver.add(pet_vars[3] == pet_map["cat"])

solver.add(name_vars[6] == name_map["Eric"])
solver.add(mother_vars[6] == mother_map["Kailyn"])
solver.add(pet_vars[6] == pet_map["rabbit"])

solver.add(name_vars[5] != name_map["Eric"])
solver.add(pet_vars[5] == pet_map["hamster"])

solver.add(name_vars[2] == name_map["Alice"])
solver.add(name_vars[4] == name_map["Carol"])
solver.add(mother_vars[4] == mother_map["Holly"])
solver.add(pet_vars[4] == pet_map["bird"])

solver.add(name_vars[1] == name_map["Bob"])
solver.add(pet_vars[1] == pet_map["dog"])

solver.add(name_vars[5] == name_map["Peter"])
solver.add(mother_vars[2] == mother_map["Sarah"])
solver.add(pet_vars[2] == pet_map["fish"])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in houses:
        name_val = [k for k, v in name_map.items() if v == model[name_vars[h]].as_long()][0]
        mother_val = [k for k, v in mother_map.items() if v == model[mother_vars[h]].as_long()][0]
        pet_val = [k for k, v in pet_map.items() if v == model[pet_vars[h]].as_long()][0]
        solution.append([str(h), name_val, mother_val, pet_val])
    print({
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": solution
        }
    })
else:
    print("No solution found")