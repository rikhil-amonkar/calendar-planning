import z3
import json

# Initialize solver
solver = z3.Solver()

# Houses are indexed from 0 to 4 (representing house numbers 1 to 5)
name = [z3.Int(f'name_{i}') for i in range(5)]
color = [z3.Int(f'color_{i}') for i in range(5)]
phone = [z3.Int(f'phone_{i}') for i in range(5)]
occupation = [z3.Int(f'occupation_{i}') for i in range(5)]

# Ensure each attribute is unique and within range
for attr in [name, color, phone, occupation]:
    for i in range(5):
        solver.add(attr[i] >= 0, attr[i] < 5)
    solver.add(z3.Distinct(attr))

# Clue 2: Bob is in house 2 (index 1)
solver.add(name[1] == 0)  # Bob is 0

# Clue 6: Lawyer uses OnePlus 9 (phone=2)
for h in range(5):
    solver.add(z3.Implies(occupation[h] == 4, phone[h] == 2))

# Clue 3: Samsung user (phone=1) is doctor (occupation=2)
for h in range(5):
    solver.add(z3.Implies(phone[h] == 1, occupation[h] == 2))

# Clue 4: Doctor (occupation=2) has color blue (0)
for h in range(5):
    solver.add(z3.Implies(occupation[h] == 2, color[h] == 0))

# Clue 8: Lawyer is to the right of doctor's house
h_doctor = z3.Int('h_doctor')
h_lawyer = z3.Int('h_lawyer')
solver.add(h_doctor >= 0, h_doctor <= 4)
solver.add(h_lawyer >= 0, h_lawyer <= 4)
solver.add(phone[h_doctor] == 1)
solver.add(occupation[h_lawyer] == 4)
for h in range(5):
    solver.add(z3.Implies(phone[h] == 1, h == h_doctor))
    solver.add(z3.Implies(occupation[h] == 4, h == h_lawyer))
solver.add(h_lawyer > h_doctor)

# Clue 1: Engineer (occupation=3) is to the right of lawyer
h_engineer = z3.Int('h_engineer')
solver.add(h_engineer >= 0, h_engineer <= 4)
solver.add(occupation[h_engineer] == 3)
for h in range(5):
    solver.add(z3.Implies(occupation[h] == 3, h == h_engineer))
solver.add(h_engineer > h_lawyer)

# Clue 10: Arnold (name=2) is engineer
solver.add(name[h_engineer] == 2)

# Clue 12: Eric (name=1) uses Google Pixel 6 (phone=4)
h_google = z3.Int('h_google')
solver.add(h_google >= 0, h_google <= 4)
solver.add(phone[h_google] == 4)
for h in range(5):
    solver.add(z3.Implies(phone[h] == 4, h == h_google))
solver.add(name[h_google] == 1)

# Clue 13: Google user is teacher (occupation=1)
solver.add(occupation[h_google] == 1)

# Clue 14: Red color (color=4) is to the right of teacher (h_google)
h_red = z3.Int('h_red')
solver.add(h_red >= 0, h_red <= 4)
solver.add(color[h_red] == 4)
for h in range(5):
    solver.add(z3.Implies(color[h] == 4, h == h_red))
solver.add(h_red > h_google)

# Clue 7: Blue (color=0) is directly left of red (color=4)
h_blue = z3.Int('h_blue')
solver.add(h_blue >= 0, h_blue <= 3)
solver.add(color[h_blue] == 0)
for h in range(5):
    solver.add(z3.Implies(color[h] == 0, h == h_blue))
solver.add(h_red == h_blue + 1)

# Clue 5: color[5] (index 4) is not green (color=1)
solver.add(color[4] != 1)

# Clue 11: Alice (name=3) loves yellow (color=3)
h_alice = z3.Int('h_alice')
solver.add(h_alice >= 0, h_alice <= 4)
solver.add(name[h_alice] == 3)
for h in range(5):
    solver.add(z3.Implies(name[h] == 3, h == h_alice))
solver.add(color[h_alice] == 3)

# Clue 9: One house between Google (h_google) and Huawei (phone=0)
h_huawei = z3.Int('h_huawei')
solver.add(h_huawei >= 0, h_huawei <= 4)
solver.add(phone[h_huawei] == 0)
for h in range(5):
    solver.add(z3.Implies(phone[h] == 0, h == h_huawei))
solver.add(z3.Or(h_google - h_huawei == 2, h_huawei - h_google == 2))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    solution = []
    name_map = {0: 'Bob', 1: 'Eric', 2: 'Arnold', 3: 'Alice', 4: 'Peter'}
    color_map = {0: 'blue', 1: 'green', 2: 'white', 3: 'yellow', 4: 'red'}
    phone_map = {0: 'huawei p50', 1: 'samsung galaxy s21', 2: 'oneplus 9', 3: 'iphone 13', 4: 'google pixel 6'}
    occupation_map = {0: 'artist', 1: 'teacher', 2: 'doctor', 3: 'engineer', 4: 'lawyer'}
    for i in range(5):
        house_num = i + 1
        n = model[name[i]].as_long()
        c = model[color[i]].as_long()
        p = model[phone[i]].as_long()
        o = model[occupation[i]].as_long()
        solution.append([
            str(house_num),
            name_map[n],
            color_map[c],
            phone_map[p],
            occupation_map[o]
        ])
    json_output = {
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": solution
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")