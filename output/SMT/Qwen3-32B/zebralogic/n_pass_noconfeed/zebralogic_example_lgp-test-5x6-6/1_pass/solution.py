import json
from z3 import *

solver = Solver()

num_houses = 5

# Define per_house and per_value arrays for each attribute
# Name: 0: Arnold, 1: Eric, 2: Alice, 3: Bob, 4: Peter
name_ph = [Int(f"name_ph_{h}") for h in range(num_houses)]
name_pv = [Int(f"name_pv_{i}") for i in range(num_houses)]
for h in range(num_houses):
    solver.add(And(name_ph[h] >= 0, name_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(name_pv[i] >= 0, name_pv[i] < num_houses))
solver.add(Distinct(name_ph))
solver.add(Distinct(name_pv))
for h in range(num_houses):
    solver.add(name_pv[name_ph[h]] == h)
for i in range(num_houses):
    solver.add(name_ph[name_pv[i]] == i)

# Vacation: 0: mountain, 1: city, 2: cruise, 3: beach, 4: camping
vacation_ph = [Int(f"vacation_ph_{h}") for h in range(num_houses)]
vacation_pv = [Int(f"vacation_pv_{i}") for i in range(num_houses)]
for h in range(num_houses):
    solver.add(And(vacation_ph[h] >= 0, vacation_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(vacation_pv[i] >= 0, vacation_pv[i] < num_houses))
solver.add(Distinct(vacation_ph))
solver.add(Distinct(vacation_pv))
for h in range(num_houses):
    solver.add(vacation_pv[vacation_ph[h]] == h)
for i in range(num_houses):
    solver.add(vacation_ph[vacation_pv[i]] == i)

# Education: 0: doctorate, 1: high school, 2: bachelor, 3: associate, 4: master
education_ph = [Int(f"education_ph_{h}") for h in range(num_houses)]
education_pv = [Int(f"education_pv_{i}") for i in range(num_houses)]
for h in range(num_houses):
    solver.add(And(education_ph[h] >= 0, education_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(education_pv[i] >= 0, education_pv[i] < num_houses))
solver.add(Distinct(education_ph))
solver.add(Distinct(education_pv))
for h in range(num_houses):
    solver.add(education_pv[education_ph[h]] == h)
for i in range(num_houses):
    solver.add(education_ph[education_pv[i]] == i)

# Color: 0: blue, 1: red, 2: white, 3: yellow, 4: green
color_ph = [Int(f"color_ph_{h}") for h in range(num_houses)]
color_pv = [Int(f"color_pv_{i}") for i in range(num_houses)]
for h in range(num_houses):
    solver.add(And(color_ph[h] >= 0, color_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(color_pv[i] >= 0, color_pv[i] < num_houses))
solver.add(Distinct(color_ph))
solver.add(Distinct(color_pv))
for h in range(num_houses):
    solver.add(color_pv[color_ph[h]] == h)
for i in range(num_houses):
    solver.add(color_ph[color_pv[i]] == i)

# PhoneModel: 0: google pixel 6, 1: iphone 13, 2: oneplus 9, 3: huawei p50, 4: samsung galaxy s21
phone_ph = [Int(f"phone_ph_{h}") for h in range(num_houses)]
phone_pv = [Int(f"phone_pv_{i}") for i in range(num_houses)]
for h in range(num_houses):
    solver.add(And(phone_ph[h] >= 0, phone_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(phone_pv[i] >= 0, phone_pv[i] < num_houses))
solver.add(Distinct(phone_ph))
solver.add(Distinct(phone_pv))
for h in range(num_houses):
    solver.add(phone_pv[phone_ph[h]] == h)
for i in range(num_houses):
    solver.add(phone_ph[phone_pv[i]] == i)

# Food: 0: grilled cheese, 1: stir fry, 2: pizza, 3: spaghetti, 4: stew
food_ph = [Int(f"food_ph_{h}") for h in range(num_houses)]
food_pv = [Int(f"food_pv_{i}") for i in range(num_houses)]
for h in range(num_houses):
    solver.add(And(food_ph[h] >= 0, food_ph[h] < num_houses))
for i in range(num_houses):
    solver.add(And(food_pv[i] >= 0, food_pv[i] < num_houses))
solver.add(Distinct(food_ph))
solver.add(Distinct(food_pv))
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