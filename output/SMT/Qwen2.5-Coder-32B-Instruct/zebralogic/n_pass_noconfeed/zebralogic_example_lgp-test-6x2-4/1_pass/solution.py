from z3 import *

# Define the variables
names = ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric']
phones = ['huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6']
houses = range(1, 7)

# Create dictionaries to map variables to Z3 variables
name_vars = {name: Int(name) for name in names}
phone_vars = {phone: Int(phone) for phone in phones}

# Create a solver instance
solver = Solver()

# Add constraints for unique placement of names and phones
solver.add(Distinct([name_vars[name] for name in names]))
solver.add(Distinct([phone_vars[phone] for phone in phones]))

# Add constraints based on the clues
# Clue 1: The person who uses an iPhone 13 is Alice.
solver.add(phone_vars['iphone 13'] == name_vars['Alice'])

# Clue 2: The person who uses a Huawei P50 is in the first house.
solver.add(phone_vars['huawei p50'] == 1)

# Clue 3: The person who uses a OnePlus 9 is in the sixth house.
solver.add(phone_vars['oneplus 9'] == 6)

# Clue 4: The person who uses a Google Pixel 6 is not in the second house.
solver.add(phone_vars['google pixel 6'] != 2)

# Clue 5: The person who uses an iPhone 13 is not in the second house.
solver.add(phone_vars['iphone 13'] != 2)

# Clue 6: There is one house between Bob and Carol.
bob_carol_dist_1 = And(phone_vars['bob'] + 2 == phone_vars['carol'], phone_vars['bob'] < phone_vars['carol'])
bob_carol_dist_2 = And(phone_vars['bob'] - 2 == phone_vars['carol'], phone_vars['bob'] > phone_vars['carol'])
solver.add(Or(bob_carol_dist_1, bob_carol_dist_2))

# Clue 7: The person who uses a Huawei P50 is Eric.
solver.add(phone_vars['huawei p50'] == name_vars['Eric'])

# Clue 8: The person who uses a Xiaomi Mi 11 is in the third house.
solver.add(phone_vars['xiaomi mi 11'] == 3)

# Clue 9: Alice is somewhere to the left of Carol.
solver.add(phone_vars['alice'] < phone_vars['carol'])

# Clue 10: Arnold is the person who uses a OnePlus 9.
solver.add(phone_vars['oneplus 9'] == name_vars['Arnold'])

# Ensure all names and phones are assigned to houses 1 through 6
for name in names:
    solver.add(And(name_vars[name] >= 1, name_vars[name] <= 6))

for phone in phones:
    solver.add(And(phone_vars[phone] >= 1, phone_vars[phone] <= 6))

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "PhoneModel"],
            "rows": []
        }
    }
    
    # Create a mapping from house number to name and phone model
    house_to_name_phone = {house: [None, None] for house in houses}
    
    for name in names:
        house_number = model[name_vars[name]].as_long()
        house_to_name_phone[house_number][0] = name
    
    for phone in phones:
        house_number = model[phone_vars[phone]].as_long()
        house_to_name_phone[house_number][1] = phone
    
    # Fill the rows in the solution
    for house in houses:
        name, phone_model = house_to_name_phone[house]
        solution["solution"]["rows"].append([str(house), name, phone_model])
    
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")