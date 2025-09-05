import json
from z3 import Solver, Int, And, Distinct, Abs, sat

def main():
    s = Solver()

    # Define person variables (house numbers from 1 to 6)
    Alice = Int("Alice")
    Arnold = Int("Arnold")
    Carol = Int("Carol")
    Peter = Int("Peter")
    Bob = Int("Bob")
    Eric = Int("Eric")
    persons = [Alice, Arnold, Carol, Peter, Bob, Eric]
    for p in persons:
        s.add(And(p >= 1, p <= 6))
    s.add(Distinct(persons))
    
    # Define phone variables (house numbers from 1 to 6)
    # Mapping:
    # "huawei p50"       -> Huawei
    # "iphone 13"        -> Iphone
    # "xiaomi mi 11"     -> Xiaomi
    # "oneplus 9"        -> OnePlus
    # "samsung galaxy s21" -> Samsung
    # "google pixel 6"   -> Google
    Huawei = Int("Huawei")
    Iphone = Int("Iphone")
    Xiaomi = Int("Xiaomi")
    OnePlus = Int("OnePlus")
    Samsung = Int("Samsung")
    Google = Int("Google")
    phones = [Huawei, Iphone, Xiaomi, OnePlus, Samsung, Google]
    for ph in phones:
        s.add(And(ph >= 1, ph <= 6))
    s.add(Distinct(phones))
    
    # Puzzle constraints based on the clues:
    # 1. The person who uses an iPhone 13 is Alice.
    s.add(Iphone == Alice)
    # 2. The person who uses a Huawei P50 is in the first house.
    s.add(Huawei == 1)
    # 3. The person who uses a OnePlus 9 is in the sixth house.
    s.add(OnePlus == 6)
    # 4. The person who uses a Google Pixel 6 is not in the second house.
    s.add(Google != 2)
    # 5. The person who uses an iPhone 13 is not in the second house.
    s.add(Iphone != 2)
    # 6. There is one house between Bob and Carol.
    s.add(Abs(Bob - Carol) == 2)
    # 7. The person who uses a Huawei P50 is Eric.
    s.add(Huawei == Eric)
    # 8. The person who uses a Xiaomi Mi 11 is in the third house.
    s.add(Xiaomi == 3)
    # 9. Alice is somewhere to the left of Carol.
    s.add(Alice < Carol)
    # 10. Arnold is the person who uses a OnePlus 9.
    s.add(OnePlus == Arnold)
    
    if s.check() == sat:
        m = s.model()
        
        # Map person variables to their names.
        person_models = [
            ("Alice", Alice),
            ("Arnold", Arnold),
            ("Carol", Carol),
            ("Peter", Peter),
            ("Bob", Bob),
            ("Eric", Eric)
        ]
        house_to_person = {}
        for name, var in person_models:
            house_num = m[var].as_long()
            house_to_person[house_num] = name

        # Map phone variables to phone model names.
        phone_models = [
            ("huawei p50", Huawei),
            ("iphone 13", Iphone),
            ("xiaomi mi 11", Xiaomi),
            ("oneplus 9", OnePlus),
            ("samsung galaxy s21", Samsung),
            ("google pixel 6", Google)
        ]
        house_to_phone = {}
        for model_name, var in phone_models:
            house_num = m[var].as_long()
            house_to_phone[house_num] = model_name
        
        # Assemble the solution rows in order of house 1 to 6.
        rows = []
        for house in range(1, 7):
            name = house_to_person.get(house, "")
            phone = house_to_phone.get(house, "")
            rows.append([str(house), name, phone])
        result = {
            "solution": {
                "header": ["House", "Name", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        # If unsolvable, output a JSON with solution set to None.
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()