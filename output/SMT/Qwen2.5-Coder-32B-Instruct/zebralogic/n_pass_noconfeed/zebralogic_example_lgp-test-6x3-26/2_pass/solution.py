from z3 import *

# Define the variables
names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
phones = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

houses = range(1, 7)

# Create the solver
solver = Solver()

# Declare variables for each house
name_vars = {house: Int(f'name_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}
phone_vars = {house: Int(f'phone_{house}') for house in houses}

# Add constraints for unique assignments
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))
solver.add(Distinct([phone_vars[house] for house in houses]))

# Map values to integers
name_map = {name: i for i, name in enumerate(names)}
height_map = {height: i for i, height in enumerate(heights)}
phone_map = {phone: i for i, phone in enumerate(phones)}

# Add constraints based on clues
# 1. Bob is directly left of the person who is tall.
solver.add(Implies(name_vars[1] == name_map["Bob"], height_vars[2] == height_map["tall"]))
for house in range(2, 6):
    solver.add(Implies(name_vars[house] == name_map["Bob"], height_vars[house + 1] == height_map["tall"]))

# 2. Peter is somewhere to the left of the person who uses an iPhone 13.
solver.add(Or([And(phone_vars[i] == phone_map["iphone 13"], name_vars[j] == name_map["Peter"]) for i in range(2, 7) for j in range(1, i)]))

# 3. The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
solver.add(Or([And(phone_vars[i] == phone_map["google pixel 6"], height_vars[j] == height_map["very short"]) for i in range(1, 6) for j in range(i + 1, 7)]))

# 4. Carol is the person who is very tall.
solver.add(Implies(name_vars[i] == name_map["Carol"], height_vars[i] == height_map["very tall"]) for i in houses)

# 5. There is one house between the person who uses a Google Pixel 6 and the person who is short.
solver.add(Or([And(phone_vars[i] == phone_map["google pixel 6"], height_vars[i + 2] == height_map["short"]) for i in range(1, 5)]))
solver.add(Or([And(phone_vars[i] == phone_map["google pixel 6"], height_vars[i - 2] == height_map["short"]) for i in range(3, 7)]))

# 6. The person who uses a Samsung Galaxy S21 is not in the first house.
solver.add(phone_vars[1] != phone_map["samsung galaxy s21"])

# 7. The person who uses a OnePlus 9 is directly left of the person who is short.
solver.add(Implies(phone_vars[1] == phone_map["oneplus 9"], height_vars[2] == height_map["short"]))
for house in range(2, 6):
    solver.add(Implies(phone_vars[house] == phone_map["oneplus 9"], height_vars[house + 1] == height_map["short"]))

# 8. The person who is tall is Arnold.
solver.add(Implies(height_vars[i] == height_map["tall"], name_vars[i] == name_map["Arnold"]) for i in houses)

# 9. The person who is super tall is in the first house.
solver.add(height_vars[1] == height_map["super tall"])

# 10. The person who uses a Xiaomi Mi 11 is Carol.
solver.add(Implies(phone_vars[i] == phone_map["xiaomi mi 11"], name_vars[i] == name_map["Carol"]) for i in houses)

# 11. The person who uses a Google Pixel 6 is somewhere to the right of Eric.
solver.add(Or([And(phone_vars[i] == phone_map["google pixel 6"], name_vars[j] == name_map["Eric"]) for i in range(2, 7) for j in range(1, i)]))

# 12. The person who is short is in the sixth house.
solver.add(height_vars[6] == height_map["short"])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        height = heights[model[height_vars[house]].as_long()]
        phone = phones[model[phone_vars[house]].as_long()]
        solution.append([str(house), name, height, phone])

    import json
    print(json.dumps({"solution": {"header": ["House", "Name", "Height", "PhoneModel"], "rows": solution}}))
else:
    print("No solution found")