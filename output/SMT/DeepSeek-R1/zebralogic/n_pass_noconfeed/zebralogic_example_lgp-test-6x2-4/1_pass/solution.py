import json
from z3 import *

def main():
    # Define the enums for Name and Phone
    Name, (Alice, Arnold, Carol, Peter, Bob, Eric) = EnumSort('Name', ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric'])
    Phone, (huawei_p50, iphone_13, xiaomi_mi_11, oneplus_9, samsung_galaxy_s21, google_pixel_6) = EnumSort('Phone', [
        'huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6'])

    # Create arrays for names and phones for each house (index 0 to 5 for houses 1 to 6)
    n = [Const(f'n_{i}', Name) for i in range(6)]
    p = [Const(f'p_{i}', Phone) for i in range(6)]

    s = Solver()

    # Distinct constraints
    s.add(Distinct(n))
    s.add(Distinct(p))

    # Clue 1: The person who uses an iPhone 13 is Alice.
    for i in range(6):
        s.add(Implies(p[i] == iphone_13, n[i] == Alice))

    # Clue 2: The person who uses a Huawei P50 is in the first house.
    s.add(p[0] == huawei_p50)

    # Clue 3: The person who uses a OnePlus 9 is in the sixth house.
    s.add(p[5] == oneplus_9)

    # Clue 4: The person who uses a Google Pixel 6 is not in the second house.
    s.add(p[1] != google_pixel_6)

    # Clue 5: The person who uses an iPhone 13 is not in the second house.
    s.add(p[1] != iphone_13)

    # Clue 6: There is one house between Bob and Carol.
    bob_house = Int('bob_house')
    carol_house = Int('carol_house')
    s.add(bob_house >= 1, bob_house <= 6)
    s.add(carol_house >= 1, carol_house <= 6)
    for i in range(6):
        s.add(If(n[i] == Bob, bob_house == i+1, True))
        s.add(If(n[i] == Carol, carol_house == i+1, True))
    s.add(Or(bob_house - carol_house == 2, carol_house - bob_house == 2))

    # Clue 7: The person who uses a Huawei P50 is Eric.
    for i in range(6):
        s.add(Implies(p[i] == huawei_p50, n[i] == Eric))

    # Clue 8: The person who uses a Xiaomi Mi 11 is in the third house.
    s.add(p[2] == xiaomi_mi_11)

    # Clue 9: Alice is somewhere to the left of Carol.
    alice_house = Int('alice_house')
    s.add(alice_house >= 1, alice_house <= 6)
    for i in range(6):
        s.add(If(n[i] == Alice, alice_house == i+1, True))
    s.add(alice_house < carol_house)

    # Clue 10: Arnold is the person who uses a OnePlus 9.
    for i in range(6):
        s.add(Implies(p[i] == oneplus_9, n[i] == Arnold))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        # Mapping from Z3 constants to strings
        name_map = {Alice: 'Alice', Arnold: 'Arnold', Carol: 'Carol', Peter: 'Peter', Bob: 'Bob', Eric: 'Eric'}
        phone_map = {
            huawei_p50: 'huawei p50',
            iphone_13: 'iphone 13',
            xiaomi_mi_11: 'xiaomi mi 11',
            oneplus_9: 'oneplus 9',
            samsung_galaxy_s21: 'samsung galaxy s21',
            google_pixel_6: 'google pixel 6'
        }
        
        rows = []
        for i in range(6):
            n_val = m.eval(n[i])
            p_val = m.eval(p[i])
            house_num = str(i+1)
            name_str = name_map[n_val]
            phone_str = phone_map[p_val]
            rows.append([house_num, name_str, phone_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()