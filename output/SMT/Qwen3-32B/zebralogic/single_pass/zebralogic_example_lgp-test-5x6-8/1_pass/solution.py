from z3 import *
import json

# Define the possible values for each attribute as lists for easy mapping later
name_list = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
housestyle_list = ["modern", "craftsman", "ranch", "victorian", "colonial"]
mother_list = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
phone_list = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
drink_list = ["coffee", "water", "root beer", "tea", "milk"]
animal_list = ["fish", "dog", "horse", "bird", "cat"]

solver = Solver()

# Create variables for each attribute for each house (0-4)
name = [Int(f'name_{i}') for i in range(5)]
housestyle = [Int(f'housestyle_{i}') for i in range(5)]
mother = [Int(f'mother_{i}') for i in range(5)]
phone = [Int(f'phone_{i}') for i in range(5)]
drink = [Int(f'drink_{i}') for i in range(5)]
animal = [Int(f'animal_{i}') for i in range(5)]

# Add constraints that all are between 0-4 and distinct
for var in [name, housestyle, mother, phone, drink, animal]:
    for i in range(5):
        solver.add(And(0 <= var[i], var[i] < 5))
    solver.add(Distinct(var))

# Now add the clues

# Clue 1: phone[0] != 1 (Google Pixel 6 not in first house)
solver.add(phone[0] != 1)

# Clue 2: Alice (name 4) drinks water (drink 1)
for i in range(5):
    solver.add(Implies(name[i] == 4, drink[i] == 1))

# Clue 3: Colonial (housestyle 4) is to the right of Huawei P50 (phone 2)
for x in range(5):
    condition = housestyle[x] == 4
    if x == 0:
        implies_condition = False
    else:
        implies_condition = Or([phone[y] == 2 for y in range(x)])
    solver.add(Implies(condition, implies_condition))

# Clue 4: Horses (animal 2) ↔ OnePlus 9 (phone 0)
for i in range(5):
    solver.add(Implies(animal[i] == 2, phone[i] == 0))
    solver.add(Implies(phone[i] == 0, animal[i] == 2))

# Clue 5: Ranch (housestyle 2) → mother Kailyn (1)
for i in range(5):
    solver.add(Implies(housestyle[i] == 2, mother[i] == 1))

# Clue 6: Root beer (drink 2) ↔ cat (animal 4)
for i in range(5):
    solver.add(Implies(drink[i] == 2, animal[i] == 4))
    solver.add(Implies(animal[i] == 4, drink[i] == 2))

# Clue 7: Colonial not in fourth house (index 3)
solver.add(housestyle[3] != 4)

# Clue 8: Bird (animal 3) in house 4 (index 3)
solver.add(animal[3] == 3)

# Clue 9: Tea (drink 3) ↔ Bob (name 3)
for i in range(5):
    solver.add(Implies(drink[i] == 3, name[i] == 3))
    solver.add(Implies(name[i] == 3, drink[i] == 3))

# Clue 10: Tea drinker (t_pos) is to the right of Kailyn's mother (m_k_pos)
m_k_pos = Int('m_k_pos')
t_pos = Int('t_pos')
solver.add(And(0 <= m_k_pos, m_k_pos < 5))
solver.add(mother[m_k_pos] == 1)
solver.add(And(0 <= t_pos, t_pos < 5))
solver.add(drink[t_pos] == 3)
solver.add(t_pos > m_k_pos)

# Clue 11: Root beer lover (r_pos) is to the left of Kailyn's mother (m_k_pos)
r_pos = Int('r_pos')
solver.add(And(0 <= r_pos, r_pos < 5))
solver.add(drink[r_pos] == 2)
solver.add(r_pos < m_k_pos)

# Clue 12: Horses (animal 2) → modern (housestyle 0)
for i in range(5):
    solver.add(Implies(animal[i] == 2, housestyle[i] == 0))

# Clue 13: iPhone 13 (phone 3) → milk (drink 4)
for i in range(5):
    solver.add(Implies(phone[i] == 3, drink[i] == 4))

# Clue 14: Dog (animal 1) → milk (drink 4)
for i in range(5):
    solver.add(Implies(animal[i] == 1, drink[i] == 4))

# Clue 15: Google Pixel 6 (phone 1) → Craftsman (housestyle 1)
for i in range(5):
    solver.add(Implies(phone[i] == 1, housestyle[i] == 1))

# Clue 16: Eric (name 0) not in second house (index 1)
solver.add(name[1] != 0)

# Clue 17: Tea (drink 3) in fourth house (index 3)
solver.add(drink[3] == 3)

# Clue 18: Horses (animal 2) in third house (index 2)
solver.add(animal[2] == 2)

# Clue 19: Modern (housestyle 0) → mother Penny (0)
for i in range(5):
    solver.add(Implies(housestyle[i] == 0, mother[i] == 0))

# Clue 20: Root beer (drink 2) → Peter (name 1)
for i in range(5):
    solver.add(Implies(drink[i] == 2, name[i] == 1))
    solver.add(Implies(name[i] == 1, drink[i] == 2))

# Clue 21: Mother Aniya (mother 4) not in fourth house (index 3)
solver.add(mother[3] != 4)

# Clue 22: Mother Janelle (mother 3) → water (drink 1)
for i in range(5):
    solver.add(Implies(mother[i] == 3, drink[i] == 1))

# Now check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Now extract the values for each house
    rows = []
    for i in range(5):
        # For each house i (0-4), which is house number i+1
        house_num = i + 1
        n = name[i].eval(model)
        hs = housestyle[i].eval(model)
        m = mother[i].eval(model)
        p = phone[i].eval(model)
        d = drink[i].eval(model)
        a = animal[i].eval(model)
        # Convert integers to their corresponding strings
        name_str = name_list[n.as_long()]
        housestyle_str = housestyle_list[hs.as_long()]
        mother_str = mother_list[m.as_long()]
        phone_str = phone_list[p.as_long()]
        drink_str = drink_list[d.as_long()]
        animal_str = animal_list[a.as_long()]
        rows.append([str(house_num), name_str, housestyle_str, mother_str, phone_str, drink_str, animal_str])
    # Output the JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")