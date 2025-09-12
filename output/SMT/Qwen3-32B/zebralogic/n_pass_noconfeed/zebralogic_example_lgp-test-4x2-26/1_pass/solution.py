import z3
import json

# Initialize Z3 solver
solver = z3.Solver()

# Define variables for each house (0 to 3 representing houses 1 to 4)
name_vars = [z3.Int(f'name_{i}') for i in range(4)]
occupation_vars = [z3.Int(f'occupation_{i}') for i in range(4)]

# All names and occupations must be unique and within valid ranges
solver.add(z3.Distinct(name_vars))
solver.add([z3.And(0 <= name_vars[i], name_vars[i] <= 3) for i in range(4)])
solver.add(z3.Distinct(occupation_vars))
solver.add([z3.And(0 <= occupation_vars[i], occupation_vars[i] <= 3) for i in range(4)])

# Clue 1: Two houses between Eric and Peter
# Clue 3: Peter is not in the first house
# This implies Eric is in house 1 (index 0) and Peter in house 4 (index 3)
solver.add(name_vars[0] == 1)  # Eric in house 1 (index 0)
solver.add(name_vars[3] == 2)  # Peter in house 4 (index 3)

# Clue 2: Peter is a teacher
solver.add(occupation_vars[3] == 3)  # Teacher is 3

# Clue 5: Alice is the artist
for j in range(4):
    solver.add(z3.Implies(name_vars[j] == 3, occupation_vars[j] == 2))  # Artist is 2

# Clue 4: One house between the doctor and Alice
for i in range(4):
    for j in range(4):
        solver.add(z3.Implies(z3.And(occupation_vars[i] == 0, name_vars[j] == 3), z3.Abs(i - j) == 2))  # Doctor is 0

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    # Map integers to names and occupations
    name_map = {0: 'Arnold', 1: 'Eric', 2: 'Peter', 3: 'Alice'}
    occupation_map = {0: 'doctor', 1: 'engineer', 2: 'artist', 3: 'teacher'}
    rows = []
    for i in range(4):
        house_num = str(i + 1)
        name_int = model[name_vars[i]].as_long()
        name = name_map[name_int]
        occ_int = model[occupation_vars[i]].as_long()
        occupation = occupation_map[occ_int]
        rows.append([house_num, name, occupation])
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")