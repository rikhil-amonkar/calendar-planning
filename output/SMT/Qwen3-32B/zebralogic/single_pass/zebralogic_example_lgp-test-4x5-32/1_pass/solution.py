from z3 import *
import json

solver = Solver()

# Variables for each house (1-4, indexes 0-3)
name = [Int(f"name_{i+1}") for i in range(4)]
hobby = [Int(f"hobby_{i+1}") for i in range(4)]
birthday = [Int(f"birthday_{i+1}") for i in range(4)]
education = [Int(f"education_{i+1}") for i in range(4)]
smoothie = [Int(f"smoothie_{i+1}") for i in range(4)]

# Add constraints for each attribute to be a permutation (distinct and 0-3)
for attr in [name, hobby, birthday, education, smoothie]:
    solver.add(Distinct(attr))
    for var in attr:
        solver.add(And(0 <= var, var <= 3))

# Clue 4: High school in house 3 (index 2)
solver.add(education[2] == 3)

# Clue 5: Watermelon not in house 3
solver.add(smoothie[2] != 1)  # watermelon is code 1

# Clue 9: Birthday in house 3 is sept (code 2)
solver.add(birthday[2] == 2)

# Clue 6: Arnold (name code 0) has associate (education code 2)
for i in range(4):
    solver.add(Implies(name[i] == 0, education[i] == 2))

# Clue 2: Eric (name code 2) has bachelor (education code 1)
for i in range(4):
    solver.add(Implies(name[i] == 2, education[i] == 1))

# Clue 10: Alice (name code 1) has cooking (hobby code 0)
for i in range(4):
    solver.add(Implies(name[i] == 1, hobby[i] == 0))

# Clue 1: Desert (smoothie 2) lover has birthday jan (1)
for i in range(4):
    solver.add(Implies(smoothie[i] == 2, birthday[i] == 1))

# Clue 3: Birthday jan (1) has education bachelor (1)
for i in range(4):
    solver.add(Implies(birthday[i] == 1, education[i] == 1))

# Clue 7: Master (0) → painting (1)
for i in range(4):
    solver.add(Implies(education[i] == 0, hobby[i] == 1))

# Clue 12: Hobby painting (1) → birthday feb (3)
for i in range(4):
    solver.add(Implies(hobby[i] == 1, birthday[i] == 3))

# Clue 8: Dragonfruit (3) and sept (birthday 2) are two apart
for i in range(4):
    for j in range(4):
        solver.add(Implies(And(smoothie[i] == 3, birthday[j] == 2), Abs(i - j) == 2))

# Clue 11: April (0) and gardening (3) are next to each other
for i in range(4):
    for j in range(4):
        solver.add(Implies(And(birthday[i] == 0, hobby[j] == 3), Abs(i - j) == 1))

if solver.check() == sat:
    model = solver.model()
    # Mapping lists
    names_list = ["Arnold", "Alice", "Eric", "Peter"]
    hobbies_list = ["cooking", "painting", "photography", "gardening"]
    birthdays_list = ["april", "jan", "sept", "feb"]
    education_list = ["master", "bachelor", "associate", "high school"]
    smoothies_list = ["cherry", "watermelon", "desert", "dragonfruit"]
    
    rows = []
    for i in range(4):
        house_num = i + 1
        n = model[name[i]].as_long()
        h = model[hobby[i]].as_long()
        b = model[birthday[i]].as_long()
        e = model[education[i]].as_long()
        s = model[smoothie[i]].as_long()
        rows.append([
            str(house_num),
            names_list[n],
            hobbies_list[h],
            birthdays_list[b],
            education_list[e],
            smoothies_list[s]
        ])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")