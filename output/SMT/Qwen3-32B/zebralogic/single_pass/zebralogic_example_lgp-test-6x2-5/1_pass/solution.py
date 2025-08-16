import z3
import json

solver = z3.Solver()

houses = list(range(1, 7))  # 1-6
name_vars = [z3.Int('name_%d' % i) for i in houses]
vacation_vars = [z3.Int('vacation_%d' % i) for i in houses]

# Domain constraints
for i in range(6):
    solver.add(z3.And(0 <= name_vars[i], name_vars[i] < 6))
    solver.add(z3.And(0 <= vacation_vars[i], vacation_vars[i] < 6))

# All names and vacations are distinct
solver.add(z3.Distinct(name_vars))
solver.add(z3.Distinct(vacation_vars))

# Clue3: Eric is in house 2 (index 1)
solver.add(name_vars[1] == 3)  # Eric is index 3 in names

# Clue4: cultural is in house 3 (index 2)
solver.add(vacation_vars[2] == 4)  # cultural is index 4

# Clue7: cultural is Peter (house3's name is Peter, index 1)
solver.add(name_vars[2] == 1)  # Peter is index 1

# Clue8: cruise is Bob. For each house, if vacation is 2 (cruise), name is 0 (Bob)
for i in range(6):
    solver.add(z3.Implies(vacation_vars[i] == 2, name_vars[i] == 0))

# Clue9: city in house4 (index 3)
solver.add(vacation_vars[3] == 3)  # city is index3

# Clue5: Bob directly left of Arnold. Check all possible positions
solver.add(z3.Or(
    z3.And(name_vars[0] == 0, name_vars[1] == 5),  # Bob in 1, Arnold 2
    z3.And(name_vars[1] == 0, name_vars[2] == 5),  # Bob 2, Arnold 3
    z3.And(name_vars[2] == 0, name_vars[3] == 5),  # Bob 3, Arnold4
    z3.And(name_vars[3] == 0, name_vars[4] == 5),  # Bob4, Arnold5
    z3.And(name_vars[4] == 0, name_vars[5] == 5)   # Bob5, Arnold6
))

# Clue2: Alice is in house1 (since Eric is in 2, and Alice is left of Eric)
solver.add(name_vars[0] == 2)  # Alice is index2

# Clue1: cultural (house3) is left of beach. So beach is in house4,5,6. Check their vacation_vars
solver.add(z3.Or(
    vacation_vars[3] == 5,  # house4
    vacation_vars[4] == 5,  # house5
    vacation_vars[5] == 5   # house6
))

# Clue6: camping not in first house
solver.add(vacation_vars[0] != 1)  # camping is index1

# Check if the solver can find a solution
if solver.check() == z3.sat:
    model = solver.model()
    # Now extract the values for each house
    solution = []
    names_list = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations_list = ["mountain", "camping", "cruise", "city", "cultural", "beach"]
    for i in range(1, 7):
        house_idx = i - 1  # index in the vars
        name_val = model[name_vars[house_idx]].as_long()
        vac_val = model[vacation_vars[house_idx]].as_long()
        solution.append([str(i), names_list[name_val], vacations_list[vac_val]])
    # Now format as required JSON
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": solution
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")