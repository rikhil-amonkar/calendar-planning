import json
from z3 import Solver, Int, And, Distinct, If

def main():
    # Define domains
    houses = list(range(1, 7))

    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = ["huawei p50", "iphone 13", "xiaomi mi 11", "oneplus 9", "samsung galaxy s21", "google pixel 6"]

    # Position variables: house index (1..6) for each attribute value
    posName = {n: Int(f"pos_name_{n}") for n in names}
    posPhone = {p: Int(f"pos_phone_{p.replace(' ', '_')}") for p in phones}

    s = Solver()

    # Domain constraints: each position is between 1 and 6
    for v in list(posName.values()) + list(posPhone.values()):
        s.add(And(v >= 1, v <= 6))

    # Uniqueness constraints
    s.add(Distinct(*posName.values()))
    s.add(Distinct(*posPhone.values()))

    # Clues:
    # 1. The person who uses an iPhone 13 is Alice.
    s.add(posPhone["iphone 13"] == posName["Alice"])

    # 2. The person who uses a Huawei P50 is in the first house.
    s.add(posPhone["huawei p50"] == 1)

    # 3. The person who uses a OnePlus 9 is in the sixth house.
    s.add(posPhone["oneplus 9"] == 6)

    # 4. The person who uses a Google Pixel 6 is not in the second house.
    s.add(posPhone["google pixel 6"] != 2)

    # 5. The person who uses an iPhone 13 is not in the second house.
    s.add(posPhone["iphone 13"] != 2)

    # 6. There is one house between Bob and Carol. |pos(Bob) - pos(Carol)| = 2
    s.add(If(posName["Bob"] > posName["Carol"],
             posName["Bob"] - posName["Carol"] == 2,
             posName["Carol"] - posName["Bob"] == 2))

    # 7. The person who uses a Huawei P50 is Eric.
    s.add(posName["Eric"] == posPhone["huawei p50"])

    # 8. The person who uses a Xiaomi Mi 11 is in the third house.
    s.add(posPhone["xiaomi mi 11"] == 3)

    # 9. Alice is somewhere to the left of Carol.
    s.add(posName["Alice"] < posName["Carol"])

    # 10. Arnold is the person who uses a OnePlus 9.
    s.add(posName["Arnold"] == posPhone["oneplus 9"])

    if s.check() != 0:  # sat
        m = s.model()

        # Build inverse mappings house -> attribute value
        name_by_house = {i: None for i in houses}
        for n in names:
            h = m[posName[n]].as_long()
            name_by_house[h] = n

        phone_by_house = {i: None for i in houses}
        for p in phones:
            h = m[posPhone[p]].as_long()
            phone_by_house[h] = p

        rows = []
        for h in houses:
            rows.append([str(h), name_by_house[h], phone_by_house[h]])

        output = {
            "solution": {
                "header": ["House", "Name", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(output, ensure_ascii=False))
    else:
        # If unsat (shouldn't happen for valid puzzle), still output valid JSON with empty rows
        output = {
            "solution": {
                "header": ["House", "Name", "PhoneModel"],
                "rows": []
            }
        }
        print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()