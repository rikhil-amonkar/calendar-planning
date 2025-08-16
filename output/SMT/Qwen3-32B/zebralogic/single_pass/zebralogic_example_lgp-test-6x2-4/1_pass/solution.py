from z3 import *
import json

def solve_puzzle():
    s = Solver()

    # Names and phones mapping
    names_list = ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric']
    phones_list = ['huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6']

    # Variables for each house (indexes 0-5 correspond to houses 1-6)
    name_in_house = [Int(f'name_house_{i+1}') for i in range(6)]
    phone_in_house = [Int(f'phone_house_{i+1}') for i in range(6)]

    # All distinct and in range
    s.add(Distinct(name_in_house))
    s.add(Distinct(phone_in_house))
    for i in range(6):
        s.add(And(0 <= name_in_house[i], name_in_house[i] < 6))
        s.add(And(0 <= phone_in_house[i], phone_in_house[i] < 6))

    # Clue 2: huawei p50 in house 1 (index 0)
    s.add(phone_in_house[0] == 0)

    # Clue 3: oneplus 9 in house 6 (index 5)
    s.add(phone_in_house[5] == 3)

    # Clue 7: Eric (index 5) in house 1 (index 0)
    s.add(name_in_house[0] == 5)

    # Clue 10: Arnold (index 1) in house 6 (index 5)
    s.add(name_in_house[5] == 1)

    # Clue 8: xiaomi mi 11 (index 2) in house 3 (index 2)
    s.add(phone_in_house[2] == 2)

    # Clue 1: Alice (name index 0) uses iphone 13 (phone index 1)
    for i in range(6):
        s.add(Implies(phone_in_house[i] == 1, name_in_house[i] == 0))

    # Clue 5: iphone 13 not in house 2 (index 1)
    s.add(phone_in_house[1] != 1)

    # Clue 4: google pixel 6 (index 5) not in house 2 (index 1)
    s.add(phone_in_house[1] != 5)

    # Clue 6: Bob (name index 4) and Carol (name index 2) have one house between
    house_bob = Int('house_bob')
    house_carol = Int('house_carol')
    s.add(Or([And(name_in_house[i] == 4, house_bob == i+1) for i in range(6)]))
    s.add(Or([And(name_in_house[i] == 2, house_carol == i+1) for i in range(6)]))
    s.add(Abs(house_bob - house_carol) == 2)

    # Clue 9: Alice's house < Carol's house
    house_alice = Int('house_alice')
    s.add(Or([And(name_in_house[i] == 0, house_alice == i+1) for i in range(6)]))
    s.add(house_alice < house_carol)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the solution
        solution = []
        for i in range(6):
            house_num = i + 1
            name_idx = model[name_in_house[i]].as_long()
            phone_idx = model[phone_in_house[i]].as_long()
            name = names_list[name_idx]
            phone = phones_list[phone_idx]
            solution.append([str(house_num), name, phone])
        return solution
    else:
        return None

solution = solve_puzzle()

# Format the solution into the required JSON
json_output = {
    "solution": {
        "header": ["House", "Name", "PhoneModel"],
        "rows": solution
    }
}

print(json.dumps(json_output, indent=2))