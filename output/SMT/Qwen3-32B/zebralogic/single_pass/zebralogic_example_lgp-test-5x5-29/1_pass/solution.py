from z3 import *

# Define EnumSorts for each attribute
Names, (Eric, Peter, Alice, Bob, Arnold) = EnumSort('Names', ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold'])
Nationalities, (Norwegian, Brit, Swede, Dane, German) = EnumSort('Nationalities', ['Norwegian', 'Brit', 'Swede', 'Dane', 'German'])
Vacations, (Cruise, Mountain, Camping, Beach, City) = EnumSort('Vacations', ['cruise', 'mountain', 'camping', 'beach', 'city'])
Educations, (Bachelor, Master, Associate, Doctorate, HighSchool) = EnumSort('Educations', ['bachelor', 'master', 'associate', 'doctorate', 'high school'])
Occupations, (Artist, Doctor, Engineer, Teacher, Lawyer) = EnumSort('Occupations', ['artist', 'doctor', 'engineer', 'teacher', 'lawyer'])

# Create variables for each house (0-based index)
name_vars = [Const(f'name_{i}', Names) for i in range(5)]
nat_vars = [Const(f'nat_{i}', Nationalities) for i in range(5)]
vac_vars = [Const(f'vac_{i}', Vacations) for i in range(5)]
edu_vars = [Const(f'edu_{i}', Educations) for i in range(5)]
occ_vars = [Const(f'occ_{i}', Occupations) for i in range(5)]

solver = Solver()

# Add uniqueness constraints for each category
for vars in [name_vars, nat_vars, vac_vars, edu_vars, occ_vars]:
    solver.add(Distinct(vars))

# Add clues as constraints
# Clue 1: Cruise implies Lawyer
for i in range(5):
    solver.add(Implies(vac_vars[i] == Cruise, occ_vars[i] == Lawyer))

# Clue 2: Beach directly left of Arnold
solver.add(Or([And(vac_vars[i] == Beach, name_vars[i+1] == Arnold) for i in range(4)]))

# Clue 3: Doctorate left of Bob
for i in range(5):
    for j in range(5):
        solver.add(Or(edu_vars[i] != Doctorate, name_vars[j] != Bob, i < j))

# Clue 4: Associate implies Cruise and Lawyer
for i in range(5):
    solver.add(Implies(edu_vars[i] == Associate, And(vac_vars[i] == Cruise, occ_vars[i] == Lawyer)))

# Clue 5: Peter not in first house
solver.add(name_vars[0] != Peter)

# Clue 6: Peter is artist
for i in range(5):
    solver.add(Implies(name_vars[i] == Peter, occ_vars[i] == Artist))

# Clue 7: Camping implies Master
for i in range(5):
    solver.add(Implies(vac_vars[i] == Camping, edu_vars[i] == Master))

# Clue 8: Dane right of Doctor
for i in range(5):
    for j in range(5):
        solver.add(Or(nat_vars[i] != Dane, occ_vars[j] != Doctor, i > j))

# Clue 9: Associate left of Engineer
solver.add(Or([And(edu_vars[i] == Associate, occ_vars[i+1] == Engineer) for i in range(4)]))

# Clue 10: Camping implies Brit
for i in range(5):
    solver.add(Implies(vac_vars[i] == Camping, nat_vars[i] == Brit))

# Clue 11: Norwegian next to Bachelor (clue 19 says Bachelor is in house 3 (index 2))
solver.add(Or(nat_vars[1] == Norwegian, nat_vars[3] == Norwegian))

# Clue 12: Artist is Swede
for i in range(5):
    solver.add(Implies(occ_vars[i] == Artist, nat_vars[i] == Swede))

# Clue 13: Bob not in fourth house (index 3)
solver.add(name_vars[3] != Bob)

# Clue 14: Camping is Eric
for i in range(5):
    solver.add(Implies(vac_vars[i] == Camping, name_vars[i] == Eric))

# Clue 15: Alice is German
for i in range(5):
    solver.add(Implies(name_vars[i] == Alice, nat_vars[i] == German))

# Clue 16: Beach left of City
for i in range(5):
    for j in range(5):
        solver.add(Implies(And(vac_vars[i] == Beach, vac_vars[j] == City), i < j))

# Clue 17: Mountain in fifth house (index 4)
solver.add(vac_vars[4] == Mountain)

# Clue 18: Cruise right of Beach
for i in range(5):
    for j in range(5):
        solver.add(Implies(And(vac_vars[i] == Beach, vac_vars[j] == Cruise), j > i))

# Clue 19: Bachelor in house 3 (index 2)
solver.add(edu_vars[2] == Bachelor)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract the solution
    solution = []
    for i in range(5):
        house = i + 1
        name = model[name_vars[i]].decl().name()
        nat = model[nat_vars[i]].decl().name()
        vac = model[vac_vars[i]].decl().name()
        edu = model[edu_vars[i]].decl().name()
        occ = model[occ_vars[i]].decl().name()
        solution.append([str(house), name, nat, vac, edu, occ])
    # Format as JSON
    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
            "rows": solution
        }
    }, indent=2))
else:
    print("No solution found.")