import z3
import json

# Initialize Z3 solver
s = z3.Solver()

# Define variables for each attribute per house (0-based index)
names = [z3.Int('names_%d' % i) for i in range(5)]
nationalities = [z3.Int('nationalities_%d' % i) for i in range(5)]
vacations = [z3.Int('vacations_%d' % i) for i in range(5)]
education = [z3.Int('education_%d' % i) for i in range(5)]
occupations = [z3.Int('occupations_%d' % i) for i in range(5)]

# Add constraints for each attribute to be permutations
for attr in [names, nationalities, vacations, education, occupations]:
    s.add(z3.Distinct(attr))
    s.add(z3.And([z3.And(0 <= x, x <= 4) for x in attr]))  # each in 0-4

# Add all the clues
# Clue 1: Cruise → lawyer
for i in range(5):
    s.add(z3.Implies(vacations[i] == 0, occupations[i] == 4))

# Clue 4: Associate's ↔ cruise
for i in range(5):
    s.add(z3.Implies(vacations[i] == 0, education[i] == 2))
    s.add(z3.Implies(education[i] == 2, vacations[i] == 0))

# Clue 2: beach left of Arnold
s.add(z3.Or([z3.And(vacations[i] == 3, names[i+1] == 4) for i in range(4)]))

# Clue 3: doctorate left of Bob
for i in range(5):
    for j in range(5):
        s.add(z3.Implies(z3.And(education[i] == 3, names[j] == 3), i < j))

# Clue 5: Peter not first
s.add(names[0] != 1)

# Clue 6: Peter is artist
for i in range(5):
    s.add(z3.Implies(names[i] == 1, occupations[i] == 0))

# Clue 7: camping → master's
for i in range(5):
    s.add(z3.Implies(vacations[i] == 2, education[i] == 1))

# Clue 8: Dane right of doctor
for i in range(5):
    for j in range(5):
        s.add(z3.Implies(z3.And(occupations[i] == 1, nationalities[j] == 3), i < j))

# Clue 9: associate left of engineer
s.add(z3.Or([z3.And(education[i] == 2, occupations[i+1] == 2) for i in range(4)]))

# Clue 10: camping → Brit
for i in range(5):
    s.add(z3.Implies(vacations[i] == 2, nationalities[i] == 1))

# Clue 11: Norwegian and bachelor next to each other
s.add(z3.Or([z3.Or(
    z3.And(nationalities[i] == 0, education[i+1] == 0),
    z3.And(nationalities[i+1] == 0, education[i] == 0)
) for i in range(4)]))

# Clue 12: artist is Swede
for i in range(5):
    s.add(z3.Implies(occupations[i] == 0, nationalities[i] == 2))

# Clue 13: Bob not in fourth
s.add(names[3] != 3)

# Clue 14: camping is Eric
for i in range(5):
    s.add(z3.Implies(vacations[i] == 2, names[i] == 0))

# Clue 15: Alice is German
for i in range(5):
    s.add(z3.Implies(names[i] == 2, nationalities[i] == 4))

# Clue 16: beach left of city
for i in range(5):
    for j in range(5):
        s.add(z3.Implies(z3.And(vacations[i] == 3, vacations[j] == 4), i < j))

# Clue 17: mountain in fifth
s.add(vacations[4] == 1)

# Clue 18: cruise right of beach
for i in range(5):
    for j in range(5):
        s.add(z3.Implies(z3.And(vacations[i] == 0, vacations[j] == 3), j < i))

# Clue 19: bachelor in third
s.add(education[2] == 0)

if s.check() == z3.sat:
    model = s.model()
    # Create mappings
    name_list = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    nat_list = ['norwegian', 'brit', 'swede', 'dane', 'german']
    vac_list = ['cruise', 'mountain', 'camping', 'beach', 'city']
    edu_list = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    occu_list = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']
    
    # For each house (0-4, which is House 1-5)
    rows = []
    for i in range(5):
        house_num = i + 1
        # Get the value for each attribute
        n_val = model[names[i]].as_long()
        name = name_list[n_val]
        
        nat_val = model[nationalities[i]].as_long()
        nat = nat_list[nat_val]
        
        vac_val = model[vacations[i]].as_long()
        vac = vac_list[vac_val]
        
        edu_val = model[education[i]].as_long()
        edu = edu_list[edu_val]
        
        occu_val = model[occupations[i]].as_long()
        occu = occu_list[occu_val]
        
        rows.append([str(house_num), name, nat, vac, edu, occu])
    
    # Build the JSON structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")