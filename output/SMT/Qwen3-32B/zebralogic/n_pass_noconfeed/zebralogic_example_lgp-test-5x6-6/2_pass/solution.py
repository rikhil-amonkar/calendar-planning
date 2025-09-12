import json
from z3 import *

solver = Solver()

num_houses = 5

# Define arrays for each attribute
# Name: 0: Arnold, 1: Eric, 2: Alice, 3: Bob, 4: Peter
name_ph = Array('name_ph', IntSort(), IntSort())
name_pv = Array('name_pv', IntSort(), IntSort())
for h in range(num_houses):
    solver.add(And(0 <= name_ph[h], name_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(0 <= name_pv[i], name_pv[i] < num_houses))
ph_values = [name_ph[i] for i in range(num_houses)]
pv_values = [name_pv[i] for i in range(num_houses)]
solver.add(Distinct(ph_values))
solver.add(Distinct(pv_values))
for h in range(num_houses):
    solver.add(name_pv[name_ph[h]] == h)
for i in range(num_houses):
    solver.add(name_ph[name_pv[i]] == i)

# Vacation: 0: mountain, 1: city, 2: cruise, 3: beach, 4: camping
vacation_ph = Array('vacation_ph', IntSort(), IntSort())
vacation_pv = Array('vacation_pv', IntSort(), IntSort())
for h in range(num_houses):
    solver.add(And(0 <= vacation_ph[h], vacation_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(0 <= vacation_pv[i], vacation_pv[i] < num_houses))
ph_values = [vacation_ph[i] for i in range(num_houses)]
pv_values = [vacation_pv[i] for i in range(num_houses)]
solver.add(Distinct(ph_values))
solver.add(Distinct(pv_values))
for h in range(num_houses):
    solver.add(vacation_pv[vacation_ph[h]] == h)
for i in range(num_houses):
    solver.add(vacation_ph[vacation_pv[i]] == i)

# Education: 0: doctorate, 1: high school, 2: bachelor, 3: associate, 4: master
education_ph = Array('education_ph', IntSort(), IntSort())
education_pv = Array('education_pv', IntSort(), IntSort())
for h in range(num_houses):
    solver.add(And(0 <= education_ph[h], education_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(0 <= education_pv[i], education_pv[i] < num_houses))
ph_values = [education_ph[i] for i in range(num_houses)]
pv_values = [education_pv[i] for i in range(num_houses)]
solver.add(Distinct(ph_values))
solver.add(Distinct(pv_values))
for h in range(num_houses):
    solver.add(education_pv[education_ph[h]] == h)
for i in range(num_houses):
    solver.add(education_ph[education_pv[i]] == i)

# Color: 0: blue, 1: red, 2: white, 3: yellow, 4: green
color_ph = Array('color_ph', IntSort(), IntSort())
color_pv = Array('color_pv', IntSort(), IntSort())
for h in range(num_houses):
    solver.add(And(0 <= color_ph[h], color_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(0 <= color_pv[i], color_pv[i] < num_houses))
ph_values = [color_ph[i] for i in range(num_houses)]
pv_values = [color_pv[i] for i in range(num_houses)]
solver.add(Distinct(ph_values))
solver.add(Distinct(pv_values))
for h in range(num_houses):
    solver.add(color_pv[color_ph[h]] == h)
for i in range(num_houses):
    solver.add(color_ph[color_pv[i]] == i)

# PhoneModel: 0: google pixel 6, 1: iphone 13, 2: oneplus 9, 3: huawei p50, 4: samsung galaxy s21
phone_ph = Array('phone_ph', IntSort(), IntSort())
phone_pv = Array('phone_pv', IntSort(), IntSort())
for h in range(num_houses):
    solver.add(And(0 <= phone_ph[h], phone_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(0 <= phone_pv[i], phone_pv[i] < num_houses))
ph_values = [phone_ph[i] for i in range(num_houses)]
pv_values = [phone_pv[i] for i in range(num_houses)]
solver.add(Distinct(ph_values))
solver.add(Distinct(pv_values))
for h in range(num_houses):
    solver.add(phone_pv[phone_ph[h]] == h)
for i in range(num_houses):
    solver.add(phone_ph[phone_pv[i]] == i)

# Food: 0: grilled cheese, 1: stir fry, 2: pizza, 3: spaghetti, 4: stew
food_ph = Array('food_ph', IntSort(), IntSort())
food_pv = Array('food_pv', IntSort(), IntSort())
for h in range(num_houses):
    solver.add(And(0 <= food_ph[h], food_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(0 <= food_pv[i], food_pv[i] < num_houses))
ph_values = [food_ph[i] for i in range(num_houses)]
pv_values = [food_pv[i] for i in range(num_houses)]
solver.add(Distinct(ph_values))
solver.add(Distinct(pv_values))
for h in range(num_houses):
    solver.add(food_pv[food_ph[h]] == h)
for i in range(num_houses):
    solver.add(food_ph[food_pv[i]] == i)

# Add constraints based on the clues
# Clue 1: Stew not in first house
solver.add(food_pv[4] != 0)

# Clue 2: Two houses between stir fry and associate
solver.add(Abs(food_pv[1] - education_pv[3]) == 3)

# Clue 3: Mountain is bachelor
solver.add(vacation_pv[0] == education_pv[2])

# Clue 4: Doctorate to the right of Bob
solver.add(education_pv[0] > name_pv[3])

# Clue 5: Samsung Galaxy S21 in house 3 (0-based index 2)
solver.add(phone_ph[2] == 4)

# Clue 6: Eric has doctorate
solver.add(education_ph[name_pv[1]] == 0)

# Clue 7: Doctorate in house 3 (0-based index 2)
solver.add(education_pv[0] == 2)

# Clue 8: Stir fry is bachelor
solver.add(food_pv[1] == education_pv[2])

# Clue 9: Doctorate's food is pizza
solver.add(food_ph[education_pv[0]] == 2)

# Clue 10: Green to the right of Peter
solver.add(color_pv[4] > name_pv[4])

# Clue 11: Camping uses iPhone 13
solver.add(phone_ph[vacation_pv[4]] == 1)

# Clue 12: Cruise is Alice
solver.add(name_ph[vacation_pv[2]] == 2)

# Clue 13: High school and Samsung Galaxy S21 have one house between
solver.add(Abs(education_pv[1] - 2) == 2)

# Clue 14: Google Pixel 6 is Arnold
solver.add(name_ph[phone_pv[0]] == 0)

# Clue 15: OnePlus 9 to the right of Huawei P50
solver.add(phone_pv[2] > phone_pv[3])

# Clue 16: Arnold has grilled cheese
solver.add(food_ph[name_pv[0]] == 0)

# Clue 17: Grilled cheese not in fourth house (0-based index 3)
solver.add(food_pv[0] != 3)

# Clue 18: Bachelor and red have two houses between
solver.add(Abs(education_pv[2] - color_pv[1]) == 3)

# Clue 19: Beach to the right of city
solver.add(vacation_pv[3] > vacation_pv[1])

# Clue 20: Green not in second house (0-based index 1)
solver.add(color_pv[4] != 1)

# Clue 21: Blue to the right of Peter
solver.add(color_pv[0] > name_pv[4])

# Clue 22: Camping and yellow have one house between
solver.add(Abs(vacation_pv[4] - color_pv[3]) == 2)

if solver.check() == sat:
    model = solver.model()
    names_list = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
    vacations_list = ["mountain", "city", "cruise", "beach", "camping"]
    educations_list = ["doctorate", "high school", "bachelor", "associate", "master"]
    colors_list = ["blue", "red", "white", "yellow", "green"]
    phone_models_list = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
    foods_list = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

    rows = []
    for h in range(num_houses):
        house_num = h + 1
        name_idx = model[name_ph[h]].as_long()
        name = names_list[name_idx]
        vacation_idx = model[vacation_ph[h]].as_long()
        vacation = vacations_list[vacation_idx]
        education_idx = model[education_ph[h]].as_long()
        education = educations_list[education_idx]
        color_idx = model[color_ph[h]].as_long()
        color = colors_list[color_idx]
        phone_idx = model[phone_ph[h]].as_long()
        phone = phone_models_list[phone_idx]
        food_idx = model[food_ph[h]].as_long()
        food = foods_list[food_idx]
        rows.append([str(house_num), name, vacation, education, color, phone, food])
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")