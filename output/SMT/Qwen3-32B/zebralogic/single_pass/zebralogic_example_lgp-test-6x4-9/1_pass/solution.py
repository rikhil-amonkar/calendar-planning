from z3 import *
import json

# Define EnumSorts for each category
Name, name_vals = EnumSort('Name', ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter'])
carol, bob, alice, arnold, eric, peter = name_vals

Phone, phone_vals = EnumSort('Phone', ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11'])
samsung_galaxy_s21, google_pixel_6, iphone_13, huawei_p50, oneplus_9, xiaomi_mi_11 = phone_vals

Nationality, nationality_vals = EnumSort('Nationality', ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit'])
swede, chinese, norwegian, dane, german, brit = nationality_vals

Color, color_vals = EnumSort('Color', ['blue', 'red', 'yellow', 'green', 'white', 'purple'])
blue, red, yellow, green, white, purple = color_vals

# Create variables for each house (1-6)
names = [Const(f'name_{i+1}', Name) for i in range(6)]
phones = [Const(f'phone_{i+1}', Phone) for i in range(6)]
nationalities = [Const(f'nationality_{i+1}', Nationality) for i in range(6)]
colors = [Const(f'color_{i+1}', Color) for i in range(6)]

s = Solver()

# Add uniqueness constraints
for lst in [names, phones, nationalities, colors]:
    s.add(Distinct(*lst))

# Clue 1: Carol not in third house
s.add(names[2] != carol)

# Clue 2: Dane in house 4, Brit in house 6
s.add(nationalities[3] == dane)
s.add(nationalities[5] == brit)

# Clue 3: Carol's color is green
for i in range(6):
    s.add(Implies(names[i] == carol, colors[i] == green))

# Clue 4: Arnold directly left of Alice
s.add(Or([And(names[i] == arnold, names[i+1] == alice) for i in range(5)]))

# Clue 5: Alice is German
for i in range(6):
    s.add(Implies(names[i] == alice, nationalities[i] == german))

# Clue 6: oneplus 9 → purple
for i in range(6):
    s.add(Implies(phones[i] == oneplus_9, colors[i] == purple))

# Clue 7: house 3 not huawei p50
s.add(phones[2] != huawei_p50)

# Clue 8: house 5 is samsung galaxy s21
s.add(phones[4] == samsung_galaxy_s21)

# Clue 9: white is to the right of red
s.add(Or([And(colors[i] == red, colors[j] == white) for i in range(6) for j in range(i+1, 6)]))

# Clue 10: house 5 is Bob
s.add(names[4] == bob)

# Clue 11: Dane's color is yellow
s.add(colors[3] == yellow)

# Clue 13: Peter's color is blue
s.add(colors[5] == blue)

# Clue 15: house 5 is directly left of iPhone 13 (house 6)
s.add(phones[5] == iphone_13)

# Clue 16: Norwegian → purple and oneplus 9
for i in range(6):
    s.add(Implies(nationalities[i] == norwegian, 
                  And(colors[i] == purple, phones[i] == oneplus_9)))

# Clue 17: Xiaomi Mi 11 → Chinese
for i in range(6):
    s.add(Implies(phones[i] == xiaomi_mi_11, nationalities[i] == chinese))

if s.check() == sat:
    m = s.model()
    rows = []
    for i in range(6):
        house_num = i + 1
        name = str(m.evaluate(names[i]))
        phone = str(m.evaluate(phones[i]))
        nationality = str(m.evaluate(nationalities[i]))
        color = str(m.evaluate(colors[i]))
        rows.append([str(house_num), name, phone, nationality, color])
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
            "rows": rows
        }
    }
    print(json.dumps(solution_dict, indent=2))
else:
    print("No solution found.")