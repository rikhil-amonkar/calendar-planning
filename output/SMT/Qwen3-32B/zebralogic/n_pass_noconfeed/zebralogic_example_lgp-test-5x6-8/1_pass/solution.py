from z3 import *
import json

def main():
    s = Solver()

    houses = 5

    # Variables for each house (1-5)
    name = [Int(f"name_{i}") for i in range(1, houses + 1)]
    housestyle = [Int(f"housestyle_{i}") for i in range(1, houses + 1)]
    mother = [Int(f"mother_{i}") for i in range(1, houses + 1)]
    phone = [Int(f"phone_{i}") for i in range(1, houses + 1)]
    drink = [Int(f"drink_{i}") for i in range(1, houses + 1)]
    animal = [Int(f"animal_{i}") for i in range(1, houses + 1)]

    # Add constraints: all distinct and in 0-4
    for attr in [name, housestyle, mother, phone, drink, animal]:
        s.add(Distinct(attr))
        for i in range(houses):
            s.add(And(0 <= attr[i], attr[i] < houses))

    # Add problem-specific constraints
    # Clue 1: Google Pixel 6 not in first house (phone[0] != 1)
    s.add(phone[0] != 1)

    # Clue 2: Alice (4) drinks water (1)
    for h in range(houses):
        s.add(Implies(drink[h] == 1, name[h] == 4))

    # Clue 3: colonial (4) to the right of huawei p50 (2)
    colonial_house = Sum([If(housestyle[h] == 4, h + 1, 0) for h in range(houses)])
    huawei_p50_house = Sum([If(phone[h] == 2, h + 1, 0) for h in range(houses)])
    s.add(colonial_house > huawei_p50_house)

    # Clue 4: horse (2) uses oneplus 9 (0)
    for h in range(houses):
        s.add(Implies(animal[h] == 2, phone[h] == 0))
        s.add(Implies(phone[h] == 0, animal[h] == 2))

    # Clue 5: ranch (2) has mother Kailyn (1)
    for h in range(houses):
        s.add(Implies(housestyle[h] == 2, mother[h] == 1))
        s.add(Implies(mother[h] == 1, housestyle[h] == 2))

    # Clue 6: root beer (2) is cat (4)
    for h in range(houses):
        s.add(Implies(drink[h] == 2, animal[h] == 4))
        s.add(Implies(animal[h] == 4, drink[h] == 2))

    # Clue 7: colonial not in fourth house (house 4, index 3)
    s.add(housestyle[3] != 4)

    # Clue 8: bird (3) in fourth house (index 3)
    s.add(animal[3] == 3)

    # Clue 9: tea (3) is Bob (3)
    for h in range(houses):
        s.add(Implies(drink[h] == 3, name[h] == 3))

    # Clue 10: tea house > Kailyn's house
    tea_house = Sum([If(drink[h] == 3, h + 1, 0) for h in range(houses)])
    kailyn_house = Sum([If(mother[h] == 1, h + 1, 0) for h in range(houses)])
    s.add(tea_house > kailyn_house)

    # Clue 11: root beer house < Kailyn's house
    root_beer_house = Sum([If(drink[h] == 2, h + 1, 0) for h in range(houses)])
    s.add(root_beer_house < kailyn_house)

    # Clue 12: horse (2) in modern (0)
    for h in range(houses):
        s.add(Implies(animal[h] == 2, housestyle[h] == 0))
        s.add(Implies(housestyle[h] == 0, animal[h] == 2))

    # Clue 13: iphone 13 (3) → milk (4)
    for h in range(houses):
        s.add(Implies(phone[h] == 3, drink[h] == 4))

    # Clue 14: dog (1) → milk (4)
    for h in range(houses):
        s.add(Implies(animal[h] == 1, drink[h] == 4))

    # Clue 15: google pixel 6 (1) → craftsman (1)
    for h in range(houses):
        s.add(Implies(phone[h] == 1, housestyle[h] == 1))

    # Clue 16: Eric (0) not in second house (h=1)
    s.add(name[1] != 0)

    # Clue 17: tea (3) in fourth house (h=3)
    s.add(drink[3] == 3)

    # Clue 18: horse (2) in third house (h=2)
    s.add(animal[2] == 2)

    # Clue 19: modern (0) → mother Penny (0)
    for h in range(houses):
        s.add(Implies(housestyle[h] == 0, mother[h] == 0))

    # Clue 20: root beer (2) → Peter (1)
    for h in range(houses):
        s.add(Implies(drink[h] == 2, name[h] == 1))
        s.add(Implies(name[h] == 1, drink[h] == 2))

    # Clue 21: Aniya (4) not in fourth house (h=3)
    s.add(mother[3] != 4)

    # Clue 22: Janelle (3) → water (1)
    for h in range(houses):
        s.add(Implies(mother[h] == 3, drink[h] == 1))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Prepare the mappings
        name_list = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
        housestyle_list = ["modern", "craftsman", "ranch", "victorian", "colonial"]
        mother_list = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
        phone_list = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
        drink_list = ["coffee", "water", "root beer", "tea", "milk"]
        animal_list = ["fish", "dog", "horse", "bird", "cat"]

        # For each house (1-5)
        rows = []
        for h in range(houses):
            house_num = h + 1
            n = m.evaluate(name[h]).as_long()
            hs = m.evaluate(housestyle[h]).as_long()
            mo = m.evaluate(mother[h]).as_long()
            ph = m.evaluate(phone[h]).as_long()
            dr = m.evaluate(drink[h]).as_long()
            an = m.evaluate(animal[h]).as_long()
            rows.append([
                str(house_num),
                name_list[n],
                housestyle_list[hs],
                mother_list[mo],
                phone_list[ph],
                drink_list[dr],
                animal_list[an]
            ])

        # Create JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                "rows": rows
            }
        }

        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()