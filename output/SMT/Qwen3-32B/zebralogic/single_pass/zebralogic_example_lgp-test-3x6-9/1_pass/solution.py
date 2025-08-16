import json
from z3 import *

solver = Solver()

# Define variables for each house (0,1,2) for each attribute
n = [Int(f"name_{i}") for i in range(3)]  # Name: Arnold(0), Eric(1), Peter(2)
c = [Int(f"car_{i}") for i in range(3)]   # CarModel: toyota(0), ford(1), tesla(2)
hs = [Int(f"housestyle_{i}") for i in range(3)]  # HouseStyle: ranch(0), colonial(1), victorian(2)
p = [Int(f"pet_{i}") for i in range(3)]   # Pet: cat(0), dog(1), fish(2)
o = [Int(f"occupation_{i}") for i in range(3)]  # Occupation: engineer(0), doctor(1), teacher(2)
v = [Int(f"vacation_{i}") for i in range(3)]  # Vacation: city(0), mountain(1), beach(2)

# Add constraints for each attribute to be in 0-2 and distinct
for var in [n, c, hs, p, o, v]:
    for i in range(3):
        solver.add(And(0 <= var[i], var[i] <= 2))
    solver.add(Distinct(var))

# Add specific clues
# Clue 1: Fish in house 1 (p[0] == 2)
solver.add(p[0] == 2)

# Clue 2: Toyota Camry in house 2 (c[1] == 0)
solver.add(c[1] == 0)

# Clue 3 and 4: v[1] is not 0 or 1, so must be 2
solver.add(v[1] == 2)

# Clue 6: housestyle of house 3 is colonial (1)
solver.add(hs[2] == 1)

# Clue 5: ranch (0) is left of Peter (n[j] == 2)
for i in range(3):
    for j in range(3):
        solver.add(Implies(And(hs[i] == 0, n[j] == 2), i < j))

# Clue 7: Arnold (0) has cat (0)
for i in range(3):
    solver.add(Implies(n[i] == 0, p[i] == 0))

# Clue 8: Eric (1) is left of mountain (v[j] == 1)
for i in range(3):
    for j in range(3):
        solver.add(Implies(And(n[i] == 1, v[j] == 1), i < j))

# Clue 9: occupation of house 3 (o[2]) is not engineer (0)
solver.add(o[2] != 0)

# Clue 10: Tesla (c[i] == 2) is left of teacher (o[j] == 2)
for i in range(3):
    for j in range(3):
        solver.add(Implies(And(c[i] == 2, o[j] == 2), i < j))

# Clue 11: if pet is dog (1), then occupation is engineer (0)
for i in range(3):
    solver.add(Implies(p[i] == 1, o[i] == 0))

if solver.check() == sat:
    model = solver.model()
    rows = []
    for i in range(3):
        house_num = i + 1
        # Name
        name_idx = model.eval(n[i]).as_long()
        name_str = ['Arnold', 'Eric', 'Peter'][name_idx]
        # CarModel
        car_idx = model.eval(c[i]).as_long()
        car_str = ['toyota camry', 'ford f150', 'tesla model 3'][car_idx]
        # HouseStyle
        hs_idx = model.eval(hs[i]).as_long()
        hs_str = ['ranch', 'colonial', 'victorian'][hs_idx]
        # Pet
        pet_idx = model.eval(p[i]).as_long()
        pet_str = ['cat', 'dog', 'fish'][pet_idx]
        # Occupation
        occ_idx = model.eval(o[i]).as_long()
        occ_str = ['engineer', 'doctor', 'teacher'][occ_idx]
        # Vacation
        vac_idx = model.eval(v[i]).as_long()
        vac_str = ['city', 'mountain', 'beach'][vac_idx]
        rows.append([str(house_num), name_str, car_str, hs_str, pet_str, occ_str, vac_str])
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")