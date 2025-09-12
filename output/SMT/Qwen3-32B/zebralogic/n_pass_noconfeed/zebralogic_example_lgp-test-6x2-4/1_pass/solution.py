import z3
import json

# Initialize the Z3 solver
solver = z3.Solver()

# Define EnumSorts for Name and PhoneModel
Name, name_consts = z3.EnumSort('Name', ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric'])
PhoneModel, phone_consts = z3.EnumSort('PhoneModel', ['huawei_p50', 'iphone_13', 'xiaomi_mi_11', 'oneplus_9', 'samsung_galaxy_s21', 'google_pixel_6'])

# Unpack constants for easier reference
Alice, Arnold, Carol, Peter, Bob, Eric = name_consts
huawei_p50, iphone_13, xiaomi_mi_11, oneplus_9, samsung_galaxy_s21, google_pixel_6 = phone_consts

# Create variables for each house's name and phone
name_vars = [z3.Const(f'name_{i}', Name) for i in range(1, 7)]  # houses 1-6
phone_vars = [z3.Const(f'phone_{i}', PhoneModel) for i in range(1, 7)]

# Add constraints that all names and phones are distinct
solver.add(z3.Distinct(name_vars))
solver.add(z3.Distinct(phone_vars))

# Clue 2: The person who uses a Huawei P50 is in the first house
solver.add(phone_vars[0] == huawei_p50)

# Clue 7: The person who uses a Huawei P50 is Eric
solver.add(name_vars[0] == Eric)

# Clue 3: The person who uses a OnePlus 9 is in the sixth house
solver.add(phone_vars[5] == oneplus_9)

# Clue 10: Arnold is the person who uses a OnePlus 9
solver.add(name_vars[5] == Arnold)

# Clue 8: The person who uses a Xiaomi Mi 11 is in the third house
solver.add(phone_vars[2] == xiaomi_mi_11)

# Clue 4: The person who uses a Google Pixel 6 is not in the second house
solver.add(phone_vars[1] != google_pixel_6)

# Clue 5: The person who uses an iPhone 13 is not in the second house
solver.add(phone_vars[1] != iphone_13)

# Clue 1: The person who uses an iPhone 13 is Alice
for i in range(6):
    solver.add(z3.Implies(phone_vars[i] == iphone_13, name_vars[i] == Alice))

# Define position variables for Bob, Carol, and Alice
pos_bob = z3.Int('pos_bob')
pos_carol = z3.Int('pos_carol')
pos_alice = z3.Int('pos_alice')

# Positions are between 1 and 6
solver.add(z3.And(1 <= pos_bob, pos_bob <= 6))
solver.add(z3.And(1 <= pos_carol, pos_carol <= 6))
solver.add(z3.And(1 <= pos_alice, pos_alice <= 6))

# Link positions to the names in each house
for i in range(6):
    solver.add(z3.Implies(name_vars[i] == Bob, pos_bob == i + 1))
    solver.add(z3.Implies(name_vars[i] == Carol, pos_carol == i + 1))
    solver.add(z3.Implies(name_vars[i] == Alice, pos_alice == i + 1))

# Clue 6: There is one house between Bob and Carol
solver.add(z3.Abs(pos_bob - pos_carol) == 2)

# Clue 9: Alice is somewhere to the left of Carol
solver.add(pos_alice < pos_carol)

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the solution
    solution = []
    for i in range(1, 7):
        house_num = str(i)
        name = model.eval(name_vars[i-1]).decl().name()
        phone = model.eval(phone_vars[i-1]).decl().name()
        solution.append([house_num, name, phone])
    # Output as JSON
    output = {
        "solution": {
            "header": ["House", "Name", "PhoneModel"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")