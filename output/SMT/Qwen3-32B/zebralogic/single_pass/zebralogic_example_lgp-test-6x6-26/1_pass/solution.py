from z3 import *
import json

# Define the possible values for each attribute and their indices
names = ["Alice", "Bob", "Carol", "Eric", "Peter", "Arnold"]
phones = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
colors = ["yellow", "red", "green", "blue", "white", "purple"]
sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

# Create variables for each house (0-5)
name_vars = [Int(f"name_{i}") for i in range(6)]
phone_vars = [Int(f"phone_{i}") for i in range(6)]
cigar_vars = [Int(f"cigar_{i}") for i in range(6)]
flower_vars = [Int(f"flower_{i}") for i in range(6)]
color_vars = [Int(f"color_{i}") for i in range(6)]
sport_vars = [Int(f"sport_{i}") for i in range(6)]

solver = Solver()

# Add constraints for distinct and range for each attribute
for vars in [name_vars, phone_vars, cigar_vars, flower_vars, color_vars, sport_vars]:
    for var in vars:
        solver.add(And(0 <= var, var <= 5))
    solver.add(Distinct(vars))

# Now add all the clues

# Clue 1: OnePlus 9 is in house 2 (index 1)
solver.add(phone_vars[1] == 5)  # oneplus 9 is index 5

# Clue 2: Xiaomi Mi 11 (2) is left of Huawei P50 (0)
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(phone_vars[i] == 2, phone_vars[j] == 0), i < j))

# Clue 3: Carol (name 2) loves carnations (flower 1)
for i in range(6):
    solver.add(Implies(name_vars[i] == 2, flower_vars[i] == 1))

# Clue 4: Purple (color 5) is directly left of Pall Mall (cigar 1)
for i in range(5):
    solver.add(Implies(color_vars[i] == 5, cigar_vars[i+1] == 1))

# Clue 5: Green (color 2) smoker is Blue Master (cigar 3)
for i in range(6):
    solver.add(Implies(color_vars[i] == 2, cigar_vars[i] == 3))

# Clue 6: Yellow (0) and blue (3) colors are next to each other
solver.add(Or(
    [And(color_vars[i] == 0, color_vars[i+1] == 3) for i in range(5)] +
    [And(color_vars[i] == 3, color_vars[i+1] == 0) for i in range(5)]
))

# Clue 7: Eric (name 3) is to the right of Samsung Galaxy S21 (phone 4)
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(name_vars[i] == 3, phone_vars[j] == 4), i > j))

# Clue 8: Two houses between Carol (name 2) and daffodils (flower 0)
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(name_vars[i] == 2, flower_vars[j] == 0), Or(j == i + 3, i == j + 3)))

# Clue 9: Prince (cigar 4) smoker loves basketball (sport 2)
for i in range(6):
    solver.add(Implies(cigar_vars[i] == 4, sport_vars[i] == 2))

# Clue 10: Dunhill (cigar 0) smoker loves volleyball (sport 3)
for i in range(6):
    solver.add(Implies(cigar_vars[i] == 0, sport_vars[i] == 3))

# Clue 11: Swimming (sport 4) is done by Google Pixel 6 (phone 1)
for i in range(6):
    solver.add(Implies(phone_vars[i] == 1, sport_vars[i] == 4))

# Clue 12: Huawei P50 (phone 0) is directly left of white (color 4)
for i in range(5):
    solver.add(Implies(phone_vars[i] == 0, color_vars[i+1] == 4))

# Clue 13: OnePlus 9 (house 2, index 1) and rose (flower 2) are next to each other
solver.add(Or(flower_vars[0] == 2, flower_vars[2] == 2))

# Clue 14: Iris (flower 5) lover is left of Eric (name 3)
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(flower_vars[i] == 5, name_vars[j] == 3), i < j))

# Clue 15: Dunhill smoker (cigar 0) is Peter (name 4)
for i in range(6):
    solver.add(Implies(cigar_vars[i] == 0, name_vars[i] == 4))

# Clue 16: Peter (name 4) loves blue (color 3)
for i in range(6):
    solver.add(Implies(name_vars[i] == 4, color_vars[i] == 3))

# Clue 17: Bob (name 1) loves tulips (flower 3)
for i in range(6):
    solver.add(Implies(name_vars[i] == 1, flower_vars[i] == 3))

# Clue 18: Alice is in house 1 (index 0)
solver.add(name_vars[0] == 0)

# Clue 19: Baseball (sport 5) lover is directly left of Blue Master (cigar 3)
for i in range(5):
    solver.add(Implies(sport_vars[i] == 5, cigar_vars[i+1] == 3))

# Clue 20: Google Pixel 6 (phone 1) is to the right of Blends (cigar 2)
for i in range(6):
    for j in range(6):
        solver.add(Implies(And(phone_vars[i] == 1, cigar_vars[j] == 2), i > j))

# Clue 21: Soccer (sport 0) is Carol's (name 2) favorite sport
for i in range(6):
    solver.add(Implies(name_vars[i] == 2, sport_vars[i] == 0))

# Clue 22: Carnations lover (flower 1) is directly left of Blends (cigar 2)
for i in range(5):
    solver.add(Implies(flower_vars[i] == 1, cigar_vars[i+1] == 2))

# Clue 23: Eric (name 3) smokes Blends (cigar 2)
for i in range(6):
    solver.add(Implies(name_vars[i] == 3, cigar_vars[i] == 2))

# Clue 24: Volleyball (sport 3) lover uses iPhone 13 (phone 3)
for i in range(6):
    solver.add(Implies(sport_vars[i] == 3, phone_vars[i] == 3))

# Now check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Extract the solution
    solution = []
    for i in range(6):
        house = i + 1
        name = names[model[name_vars[i]].as_long()]
        phone = phones[model[phone_vars[i]].as_long()]
        cigar = cigars[model[cigar_vars[i]].as_long()]
        flower = flowers[model[flower_vars[i]].as_long()]
        color = colors[model[color_vars[i]].as_long()]
        sport = sports[model[sport_vars[i]].as_long()]
        solution.append([str(house), name, phone, cigar, flower, color, sport])
    # Output the JSON
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
            "rows": solution
        }
    }, indent=2))
else:
    print("No solution found.")