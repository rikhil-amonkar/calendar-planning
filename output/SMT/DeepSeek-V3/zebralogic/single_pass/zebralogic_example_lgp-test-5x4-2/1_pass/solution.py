from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
colors = ["blue", "green", "white", "yellow", "red"]
phone_models = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
occupations = ["artist", "teacher", "doctor", "engineer", "lawyer"]

# Create dictionaries to hold the variables for each attribute per house
name = {h: String(f"name_{h}") for h in houses}
color = {h: String(f"color_{h}") for h in houses}
phone = {h: String(f"phone_{h}") for h in houses}
occupation = {h: String(f"occupation_{h}") for h in houses}

# Add constraints for uniqueness of each attribute
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([color[h] for h in houses]))
s.add(Distinct([phone[h] for h in houses]))
s.add(Distinct([occupation[h] for h in houses]))

# Each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([color[h] == c for c in colors]))
    s.add(Or([phone[h] == p for p in phone_models]))
    s.add(Or([occupation[h] == o for o in occupations]))

# Apply the clues
# Clue 2: Bob is in the second house.
s.add(name[2] == "Bob")

# Clue 12: The person who uses a Google Pixel 6 is Eric.
for h in houses:
    s.add(Implies(phone[h] == "google pixel 6", name[h] == "Eric"))

# Clue 13: The person who uses a Google Pixel 6 is the person who is a teacher.
for h in houses:
    s.add(Implies(phone[h] == "google pixel 6", occupation[h] == "teacher"))

# Clue 3: The person who uses a Samsung Galaxy S21 is the person who is a doctor.
for h in houses:
    s.add(Implies(phone[h] == "samsung galaxy s21", occupation[h] == "doctor"))

# Clue 4: The person who is a doctor is the person who loves blue.
for h in houses:
    s.add(Implies(occupation[h] == "doctor", color[h] == "blue"))

# Clue 6: The person who is a lawyer is the person who uses a OnePlus 9.
for h in houses:
    s.add(Implies(occupation[h] == "lawyer", phone[h] == "oneplus 9"))

# Clue 7: The person who loves blue is directly left of the person whose favorite color is red.
for h in range(1, 5):
    s.add(Implies(color[h] == "blue", color[h+1] == "red"))

# Clue 8: The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21.
# This means the house number of the lawyer is greater than the house number of the Samsung user.
samsung_house = Int("samsung_house")
lawyer_house = Int("lawyer_house")
s.add(And([Or(phone[h] == "samsung galaxy s21", samsung_house == h) for h in houses]))
s.add(And([Or(occupation[h] == "lawyer", lawyer_house == h) for h in houses]))
s.add(lawyer_house > samsung_house)

# Clue 1: The person who is an engineer is somewhere to the right of the person who is a lawyer.
# This means the house number of the engineer is greater than the house number of the lawyer.
engineer_house = Int("engineer_house")
s.add(And([Or(occupation[h] == "engineer", engineer_house == h) for h in houses]))
s.add(engineer_house > lawyer_house)

# Clue 10: Arnold is the person who is an engineer.
for h in houses:
    s.add(Implies(name[h] == "Arnold", occupation[h] == "engineer"))

# Clue 11: Alice is the person who loves yellow.
for h in houses:
    s.add(Implies(name[h] == "Alice", color[h] == "yellow"))

# Clue 5: The person whose favorite color is green is not in the fifth house.
s.add(And([Implies(color[h] == "green", h != 5) for h in houses]))

# Clue 9: There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50.
# This means if Google is in house h, Huawei is in house h+2, or vice versa.
for h in range(1, 4):
    s.add(Or(
        And(phone[h] == "google pixel 6", phone[h+2] == "huawei p50"),
        And(phone[h] == "huawei p50", phone[h+2] == "google pixel 6")
    ))

# Clue 14: The person whose favorite color is red is somewhere to the right of the person who is a teacher.
# This means the house number of red is greater than the house number of the teacher.
teacher_house = Int("teacher_house")
red_house = Int("red_house")
s.add(And([Or(occupation[h] == "teacher", teacher_house == h) for h in houses]))
s.add(And([Or(color[h] == "red", red_house == h) for h in houses]))
s.add(red_house > teacher_house)

# Solve the constraints
if s.check() == sat:
    m = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            str(m.evaluate(name[h])),
            str(m.evaluate(color[h])),
            str(m.evaluate(phone[h])),
            str(m.evaluate(occupation[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")