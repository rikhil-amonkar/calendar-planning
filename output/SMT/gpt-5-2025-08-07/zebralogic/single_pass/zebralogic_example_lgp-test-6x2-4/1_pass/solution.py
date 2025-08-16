import json
from z3 import Solver, Int, And, Or, Distinct, sat

def solve():
    # Entities
    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = [
        "huawei p50",
        "iphone 13",
        "xiaomi mi 11",
        "oneplus 9",
        "samsung galaxy s21",
        "google pixel 6",
    ]

    # Index mapping helpers
    name_idx = {n: i for i, n in enumerate(names)}
    phone_idx = {p: i for i, p in enumerate(phones)}

    # Position variables: house indices are 0..5 (representing houses 1..6)
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_phone = {p: Int(f"pos_phone_{p.replace(' ', '_')}") for p in phones}

    s = Solver()

    # Domain constraints
    for n in names:
        s.add(And(pos_name[n] >= 0, pos_name[n] <= 5))
    for p in phones:
        s.add(And(pos_phone[p] >= 0, pos_phone[p] <= 5))

    # All persons in unique houses, all phones in unique houses
    s.add(Distinct([pos_name[n] for n in names]))
    s.add(Distinct([pos_phone[p] for p in phones]))

    # Clues:
    # 1. The person who uses an iPhone 13 is Alice.
    s.add(pos_phone["iphone 13"] == pos_name["Alice"])

    # 2. The person who uses a Huawei P50 is in the first house.
    s.add(pos_phone["huawei p50"] == 0)

    # 3. The person who uses a OnePlus 9 is in the sixth house.
    s.add(pos_phone["oneplus 9"] == 5)

    # 4. The person who uses a Google Pixel 6 is not in the second house.
    s.add(pos_phone["google pixel 6"] != 1)

    # 5. The person who uses an iPhone 13 is not in the second house.
    s.add(pos_phone["iphone 13"] != 1)

    # 6. There is one house between Bob and Carol.
    s.add(Or(pos_name["Bob"] == pos_name["Carol"] + 2, pos_name["Carol"] == pos_name["Bob"] + 2))

    # 7. The person who uses a Huawei P50 is Eric.
    s.add(pos_phone["huawei p50"] == pos_name["Eric"])

    # 8. The person who uses a Xiaomi Mi 11 is in the third house.
    s.add(pos_phone["xiaomi mi 11"] == 2)

    # 9. Alice is somewhere to the left of Carol.
    s.add(pos_name["Alice"] < pos_name["Carol"])

    # 10. Arnold is the person who uses a OnePlus 9.
    s.add(pos_name["Arnold"] == pos_phone["oneplus 9"])

    if s.check() != sat:
        raise RuntimeError("No solution found.")

    m = s.model()

    # Build reverse lookup: for each house, find the unique name and phone
    # House indices 0..5 -> names/phones
    house_to_name = [""] * 6
    house_to_phone = [""] * 6

    for n in names:
        idx = m.evaluate(pos_name[n]).as_long()
        house_to_name[idx] = n

    for p in phones:
        idx = m.evaluate(pos_phone[p]).as_long()
        house_to_phone[idx] = p

    # Prepare JSON output
    result = {
        "solution": {
            "header": ["House", "Name", "PhoneModel"],
            "rows": []
        }
    }

    for i in range(6):
        row = [str(i + 1), house_to_name[i], house_to_phone[i]]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve()