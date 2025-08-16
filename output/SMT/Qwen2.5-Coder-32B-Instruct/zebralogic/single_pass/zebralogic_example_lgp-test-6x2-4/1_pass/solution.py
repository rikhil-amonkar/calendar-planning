from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each house
house_names = [Int(f'house_{i}_name') for i in range(1, 7)]
house_phones = [Int(f'house_{i}_phone') for i in range(1, 7)]

# Define constants for names and phones
names = {'Alice': 1, 'Arnold': 2, 'Carol': 3, 'Peter': 4, 'Bob': 5, 'Eric': 6}
phones = {'huawei p50': 1, 'iphone 13': 2, 'xiaomi mi 11': 3, 'oneplus 9': 4, 'samsung galaxy s21': 5, 'google pixel 6': 6}

# Add constraints for unique names and phones
solver.add(Distinct(house_names))
solver.add(Distinct(house_phones))

# Clue 1: The person who uses an iPhone 13 is Alice.
solver.add(house_phones[0] == phones['iphone 13'])
solver.add(house_names[0] == names['Alice'])

# Clue 2: The person who uses a Huawei P50 is in the first house.
solver.add(house_phones[0] == phones['huawei p50'])

# Clue 3: The person who uses a OnePlus 9 is in the sixth house.
solver.add(house_phones[5] == phones['oneplus 9'])

# Clue 4: The person who uses a Google Pixel 6 is not in the second house.
solver.add(house_phones[1] != phones['google pixel 6'])

# Clue 5: The person who uses an iPhone 13 is not in the second house.
solver.add(house_phones[1] != phones['iphone 13'])

# Clue 6: There is one house between Bob and Carol.
bob_carol_dist = Or(
    And(house_names.index(names['Bob']) + 2 == house_names.index(names['Carol'])),
    And(house_names.index(names['Carol']) + 2 == house_names.index(names['Bob']))
)
solver.add(bob_carol_dist)

# Clue 7: The person who uses a Huawei P50 is Eric.
solver.add(house_names[0] == names['Eric'])

# Clue 8: The person who uses a Xiaomi Mi 11 is in the third house.
solver.add(house_phones[2] == phones['xiaomi mi 11'])

# Clue 9: Alice is somewhere to the left of Carol.
alice_left_carol = Or(
    And(house_names.index(names['Alice']) < house_names.index(names['Carol']))
)
solver.add(alice_left_carol)

# Clue 10: Arnold is the person who uses a OnePlus 9.
solver.add(house_names[5] == names['Arnold'])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = []
    for i in range(6):
        house_number = i + 1
        name_value = [k for k, v in names.items() if v == model[house_names[i]].as_long()][0]
        phone_value = [k for k, v in phones.items() if v == model[house_phones[i]].as_long()][0]
        solution.append([str(house_number), name_value, phone_value])
    
    # Output the solution as JSON
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "PhoneModel"],' +
          f'"rows": {solution}' +
          '}'
          '}')
else:
    print("No solution found")