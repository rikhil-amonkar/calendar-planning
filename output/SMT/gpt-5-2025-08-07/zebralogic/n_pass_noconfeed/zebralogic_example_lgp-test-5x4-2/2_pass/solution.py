import json
from z3 import Solver, Int, Distinct, Or, sat

def main():
    # Define attributes
    houses = [1, 2, 3, 4, 5]

    Names = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    Colors = ["blue", "green", "white", "yellow", "red"]
    Phones = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    Jobs = ["artist", "teacher", "doctor", "engineer", "lawyer"]

    # Create Z3 variables for the position (house number) of each attribute value
    def vname(prefix, key):
        return f"{prefix}_{key.replace(' ', '_').replace('-', '_').lower()}"

    pos_name = {n: Int(vname("name", n)) for n in Names}
    pos_color = {c: Int(vname("color", c)) for c in Colors}
    pos_phone = {p: Int(vname("phone", p)) for p in Phones}
    pos_job = {j: Int(vname("job", j)) for j in Jobs}

    s = Solver()

    # Domains: each position is in 1..5
    for d in [pos_name, pos_color, pos_phone, pos_job]:
        for var in d.values():
            s.add(var >= 1, var <= 5)

    # Uniqueness within each category
    s.add(Distinct([pos_name[n] for n in Names]))
    s.add(Distinct([pos_color[c] for c in Colors]))
    s.add(Distinct([pos_phone[p] for p in Phones]))
    s.add(Distinct([pos_job[j] for j in Jobs]))

    # Clues:
    # 1. Engineer is somewhere to the right of Lawyer.
    s.add(pos_job["engineer"] > pos_job["lawyer"])

    # 2. Bob is in the second house.
    s.add(pos_name["Bob"] == 2)

    # 3. Samsung Galaxy S21 user is the doctor.
    s.add(pos_phone["samsung galaxy s21"] == pos_job["doctor"])

    # 4. Doctor loves blue.
    s.add(pos_job["doctor"] == pos_color["blue"])

    # 5. Green is not in the fifth house.
    s.add(pos_color["green"] != 5)

    # 6. Lawyer uses a OnePlus 9.
    s.add(pos_job["lawyer"] == pos_phone["oneplus 9"])

    # 7. Blue is directly left of Red.
    s.add(pos_color["blue"] + 1 == pos_color["red"])

    # 8. Lawyer is to the right of Samsung Galaxy S21.
    s.add(pos_job["lawyer"] > pos_phone["samsung galaxy s21"])

    # 9. One house between Google Pixel 6 and Huawei P50.
    s.add(Or(pos_phone["google pixel 6"] == pos_phone["huawei p50"] + 2,
             pos_phone["google pixel 6"] == pos_phone["huawei p50"] - 2))

    # 10. Arnold is the engineer.
    s.add(pos_name["Arnold"] == pos_job["engineer"])

    # 11. Alice loves yellow.
    s.add(pos_name["Alice"] == pos_color["yellow"])

    # 12. Google Pixel 6 user is Eric.
    s.add(pos_phone["google pixel 6"] == pos_name["Eric"])

    # 13. Google Pixel 6 user is the teacher.
    s.add(pos_phone["google pixel 6"] == pos_job["teacher"])

    # 14. Red is somewhere to the right of the teacher.
    s.add(pos_color["red"] > pos_job["teacher"])

    if s.check() != sat:
        print(json.dumps({"error": "No solution found"}))
        return

    m = s.model()

    # Helper to find the attribute value assigned to a given house
    def find_by_house(position_map, values, house):
        for val in values:
            if m[position_map[val]].as_long() == house:
                return val
        return None

    rows = []
    for h in houses:
        name = find_by_house(pos_name, Names, h)
        color = find_by_house(pos_color, Colors, h)
        phone = find_by_house(pos_phone, Phones, h)
        job = find_by_house(pos_job, Jobs, h)
        rows.append([str(h), name, color, phone, job])

    output = {
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()