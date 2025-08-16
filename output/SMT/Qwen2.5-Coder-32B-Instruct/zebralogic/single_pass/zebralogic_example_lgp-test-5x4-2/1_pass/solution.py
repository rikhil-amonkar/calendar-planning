from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [Int(f"house_{i}") for i in range(1, 6)]
names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
colors = ['blue', 'green', 'white', 'yellow', 'red']
phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']

# Maps for each attribute
name_map = {name: Int(f"name_{name}") for name in names}
color_map = {color: Int(f"color_{color}") for color in colors}
phone_map = {phone: Int(f"phone_{phone}") for phone in phones}
occupation_map = {occupation: Int(f"occupation_{occupation}") for occupation in occupations}

# Ensure each attribute is assigned to a unique house
solver.add(Distinct(houses))
solver.add(Distinct(name_map.values()))
solver.add(Distinct(color_map.values()))
solver.add(Distinct(phone_map.values()))
solver.add(Distinct(occupation_map.values()))

# Map each attribute to a house number
for i in range(5):
    solver.add(houses[i] == i + 1)
    solver.add(Or([name_map[name] == i + 1 for name in names]))
    solver.add(Or([color_map[color] == i + 1 for color in colors]))
    solver.add(Or([phone_map[phone] == i + 1 for phone in phones]))
    solver.add(Or([occupation_map[occupation] == i + 1 for occupation in occupations]))

# Apply clues
# 1. The person who is an engineer is somewhere to the right of the person who is a lawyer.
solver.add(occupation_map['engineer'] > occupation_map['lawyer'])

# 2. Bob is in the second house.
solver.add(name_map['Bob'] == 2)

# 3. The person who uses a Samsung Galaxy S21 is the person who is a doctor.
solver.add(phone_map['samsung galaxy s21'] == occupation_map['doctor'])

# 4. The person who is a doctor is the person who loves blue.
solver.add(occupation_map['doctor'] == color_map['blue'])

# 5. The person whose favorite color is green is not in the fifth house.
solver.add(color_map['green'] != 5)

# 6. The person who is a lawyer is the person who uses a OnePlus 9.
solver.add(occupation_map['lawyer'] == phone_map['oneplus 9'])

# 7. The person who loves blue is directly left of the person whose favorite color is red.
solver.add(color_map['blue'] + 1 == color_map['red'])

# 8. The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21.
solver.add(occupation_map['lawyer'] > phone_map['samsung galaxy s21'])

# 9. There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50.
solver.add(Abs(phone_map['google pixel 6'] - phone_map['huawei p50']) == 2)

# 10. Arnold is the person who is an engineer.
solver.add(name_map['Arnold'] == occupation_map['engineer'])

# 11. Alice is the person who loves yellow.
solver.add(name_map['Alice'] == color_map['yellow'])

# 12. The person who uses a Google Pixel 6 is Eric.
solver.add(phone_map['google pixel 6'] == name_map['Eric'])

# 13. The person who uses a Google Pixel 6 is the person who is a teacher.
solver.add(phone_map['google pixel 6'] == occupation_map['teacher'])

# 14. The person whose favorite color is red is somewhere to the right of the person who is a teacher.
solver.add(color_map['red'] > occupation_map['teacher'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Create a mapping from house number to attributes
    house_to_attributes = {}
    for i in range(5):
        house_number = i + 1
        name = next(name for name, var in name_map.items() if model[var] == house_number)
        color = next(color for color, var in color_map.items() if model[var] == house_number)
        phone = next(phone for phone, var in phone_map.items() if model[var] == house_number)
        occupation = next(occupation for occupation, var in occupation_map.items() if model[var] == house_number)
        house_to_attributes[house_number] = [str(house_number), name, color, phone, occupation]

    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": [house_to_attributes[i] for i in range(1, 6)]
        }
    }

    # Print the solution as JSON
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")