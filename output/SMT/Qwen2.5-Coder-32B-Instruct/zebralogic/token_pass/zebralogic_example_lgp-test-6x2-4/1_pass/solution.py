from z3 import *

# Define the variables for names and phone models
names = ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric']
phone_models = ['huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6']

# Create Z3 variables for each house
house_names = [String(f'name_{i}') for i in range(1, 7)]
house_phones = [String(f'phone_{i}') for i in range(1, 7)]

# Create a Z3 solver instance
solver = Solver()

# Add constraints based on the clues
# Clue 1: Alice uses an iPhone 13
solver.add(house_names[i] == 'Alice') == (house_phones[i] == 'iphone 13') for i in range(6) if i == house_names.index('Alice')
solver.add(house_phones[house_names.index('Alice')] == 'iphone 13')

# Clue 2: The person who uses a Huawei P50 is in the first house
solver.add(house_phones[0] == 'huawei p50')

# Clue 3: The person who uses a OnePlus 9 is in the sixth house
solver.add(house_phones[5] == 'oneplus 9')

# Clue 4: The person who uses a Google Pixel 6 is not in the second house
solver.add(house_phones[1] != 'google pixel 6')

# Clue 5: The person who uses an iPhone 13 is not in the second house
solver.add(house_phones[1] != 'iphone 13')

# Clue 6: There is one house between Bob and Carol
bob_index = Int('bob_index')
carol_index = Int('carol_index')
solver.add(bob_index >= 0)
solver.add(carol_index >= 0)
solver.add(bob_index < 6)
solver.add(carol_index < 6)
solver.add(Or(bob_index + 2 == carol_index, carol_index + 2 == bob_index))
solver.add(house_names[bob_index] == 'Bob')
solver.add(house_names[carol_index] == 'Carol')

# Clue 7: The person who uses a Huawei P50 is Eric
solver.add(house_names[house_phones.index('huawei p50')] == 'Eric')

# Clue 8: The person in the third house uses a Xiaomi Mi 11
solver.add(house_phones[2] == 'xiaomi mi 11')

# Clue 9: Alice is somewhere to the left of Carol
alice_index = Int('alice_index')
carol_index = Int('carol_index')
solver.add(alice_index >= 0)
solver.add(carol_index >= 0)
solver.add(alice_index < 6)
solver.add(carol_index < 6)
solver.add(house_names[alice_index] == 'Alice')
solver.add(house_names[carol_index] == 'Carol')
solver.add(alice_index < carol_index)

# Clue 10: Arnold is the person who uses a OnePlus 9
solver.add(house_names[house_phones.index('oneplus 9')] == 'Arnold')

# Ensure each name and phone model is unique
solver.add(Distinct(house_names))
solver.add(Distinct(house_phones))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(6):
        name = model[house_names[i]].as_string()[1:-1]  # Remove quotes from the string
        phone = model[house_phones[i]].as_string()[1:-1]  # Remove quotes from the string
        solution.append([str(i+1), name, phone])
    
    print({
        "solution": {
            "header": ["House", "Name", "PhoneModel"],
            "rows": solution
        }
    })
else:
    print("No solution found")