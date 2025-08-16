from z3 import Solver, Distinct, And, Or, Implies, Int, sat

solver = Solver()

names = [Int(f'name_{i}') for i in range(3)]
education = [Int(f'edu_{i}') for i in range(3)]
occupation = [Int(f'occ_{i}') for i in range(3)]

# All variables are between 0 and 2
for var in names + education + occupation:
    solver.add(And(0 <= var, var <= 2))

# All distinct per category
solver.add(Distinct(names))
solver.add(Distinct(education))
solver.add(Distinct(occupation))

# Clue 3: Peter (name 0) has high school (edu 2)
for i in range(3):
    solver.add(Implies(names[i] == 0, education[i] == 2))

# Clue 4: doctor (occ 1) has bachelor (edu 0)
for i in range(3):
    solver.add(Implies(occupation[i] == 1, education[i] == 0))

# Clue 1: teacher (occ 0) is directly left of associate (edu 1)
solver.add(Or(
    And(occupation[0] == 0, education[1] == 1),
    And(occupation[1] == 0, education[2] == 1)
))

# Clue 2: associate (edu 1) and Eric (name 1) are next to each other
solver.add(Or(
    Or(And(education[0] == 1, names[1] == 1), And(education[1] == 1, names[0] == 1)),
    Or(And(education[1] == 1, names[2] == 1), And(education[2] == 1, names[1] == 1))
))

if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(3):
        name_val = model[names[i]].as_long()
        edu_val = model[education[i]].as_long()
        occ_val = model[occupation[i]].as_long()
        solution.append([
            str(i+1),
            ["Peter", "Eric", "Arnold"][name_val],
            ["bachelor", "associate", "high school"][edu_val],
            ["teacher", "doctor", "engineer"][occ_val]
        ])
    json_output = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": solution
        }
    }
    print(json_output)
else:
    print("No solution found.")