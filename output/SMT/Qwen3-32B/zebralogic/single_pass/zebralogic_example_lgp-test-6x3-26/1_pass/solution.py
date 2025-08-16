from z3 import *

names = [Int(f"name_{i}") for i in range(6)]
heights = [Int(f"height_{i}") for i in range(6)]
phones = [Int(f"phone_{i}") for i in range(6)]

solver = Solver()

# Add constraints for each attribute to be 0-5 and distinct
for attr in [names, heights, phones]:
    for i in range(6):
        solver.add(And(attr[i] >= 0, attr[i] < 6))
    solver.add(Distinct(attr))

# Clue 12: short is in house 6 (index 5)
solver.add(heights[5] == 5)

# Clue 5: Google Pixel 6 is in house 4 (index 3)
solver.add(phones[3] == 1)  # phone index 1 is google pixel 6

# Clue 7: OnePlus 9 is in house 5 (index 4)
solver.add(phones[4] == 0)  # phone index 0 is oneplus 9

# Clue 9: super tall in first house (index 0)
solver.add(heights[0] == 2)  # height index 2 is super tall

# Clue 3: very short (height 4) is to the right of Google Pixel 6 (index 3)
# Since Google Pixel 6 is at 3, very short must be at 4 (since 5 is short)
solver.add(heights[4] == 4)  # height index 4 is very short

# Clue 4 and 10: Carol's constraints
carol_pos = Int('carol_pos')
for i in range(6):
    solver.add(Implies(names[i] == 5, carol_pos == i))
solver.add(heights[carol_pos] == 0)  # very tall (height 0)
solver.add(phones[carol_pos] == 5)  # xiaomi mi 11 (phone 5)

# Clue 8: Arnold's height is tall (1)
arnold_pos = Int('arnold_pos')
for i in range(6):
    solver.add(Implies(names[i] == 4, arnold_pos == i))
solver.add(heights[arnold_pos] == 1)

# Clue 1: Bob is directly left of Arnold
bob_pos = Int('bob_pos')
for i in range(6):
    solver.add(Implies(names[i] == 2, bob_pos == i))
solver.add(arnold_pos == bob_pos + 1)

# Clue 11: Google Pixel 6 (index 3) is to the right of Eric
eric_pos = Int('eric_pos')
for i in range(6):
    solver.add(Implies(names[i] == 1, eric_pos == i))
solver.add(3 > eric_pos)  # since google_pixel_6 is at index 3

# Clue 2: Peter is to the left of iPhone 13
peter_pos = Int('peter_pos')
iphone_13_pos = Int('iphone_13_pos')
for i in range(6):
    solver.add(Implies(names[i] == 3, peter_pos == i))
for i in range(6):
    solver.add(Implies(phones[i] == 3, iphone_13_pos == i))
solver.add(peter_pos < iphone_13_pos)

# Clue 6: Samsung Galaxy S21 (phone 2) not in first house (index 0)
solver.add(phones[0] != 2)

# Now check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Extract the assignments
    result = []
    for i in range(6):
        name_val = model.eval(names[i]).as_long()
        height_val = model.eval(heights[i]).as_long()
        phone_val = model.eval(phones[i]).as_long()
        result.append([
            str(i + 1),
            ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"][name_val],
            ["very tall", "tall", "super tall", "average", "very short", "short"][height_val],
            ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"][phone_val]
        ])
    # Format as JSON
    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Height", "PhoneModel"],
            "rows": result
        }
    }, indent=2))
else:
    print("No solution found.")