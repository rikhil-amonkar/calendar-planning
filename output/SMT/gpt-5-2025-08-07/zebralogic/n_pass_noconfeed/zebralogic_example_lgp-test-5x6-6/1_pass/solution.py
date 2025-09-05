import json
from z3 import Solver, Int, Distinct, And, Or, Abs, sat

def main():
    houses = [1, 2, 3, 4, 5]

    Names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
    Vacations = ["mountain", "city", "cruise", "beach", "camping"]
    Educations = ["doctorate", "high school", "bachelor", "associate", "master"]
    Colors = ["blue", "red", "white", "yellow", "green"]
    Phones = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
    Foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

    # Create Z3 variables for positions (1..5) of each attribute value
    pos_name = {n: Int(f"pos_name_{n.replace(' ', '_')}") for n in Names}
    pos_vac = {v: Int(f"pos_vac_{v.replace(' ', '_')}") for v in Vacations}
    pos_edu = {e: Int(f"pos_edu_{e.replace(' ', '_')}") for e in Educations}
    pos_color = {c: Int(f"pos_color_{c.replace(' ', '_')}") for c in Colors}
    pos_phone = {p: Int(f"pos_phone_{p.replace(' ', '_').replace('-', '_')}") for p in Phones}
    pos_food = {f: Int(f"pos_food_{f.replace(' ', '_')}") for f in Foods}

    s = Solver()

    # Domain constraints: each position is between 1 and 5
    for d in [pos_name, pos_vac, pos_edu, pos_color, pos_phone, pos_food]:
        for v in d.values():
            s.add(And(v >= 1, v <= 5))

    # AllDifferent within each category
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_vac.values()))
    s.add(Distinct(*pos_edu.values()))
    s.add(Distinct(*pos_color.values()))
    s.add(Distinct(*pos_phone.values()))
    s.add(Distinct(*pos_food.values()))

    # Helper for "one house between" and "two houses between"
    def diff_eq(a, b, d):
        return Abs(a - b) == d

    # Clues
    # 1. The person who loves the stew is not in the first house.
    s.add(pos_food["stew"] != 1)

    # 2. There are two houses between the person who loves stir fry and the person with an associate's degree.
    s.add(diff_eq(pos_food["stir fry"], pos_edu["associate"], 3))

    # 3. The person who enjoys mountain retreats is the person with a bachelor's degree.
    s.add(pos_vac["mountain"] == pos_edu["bachelor"])

    # 4. The person with a doctorate is somewhere to the right of Bob.
    s.add(pos_edu["doctorate"] > pos_name["Bob"])

    # 5. The person who uses a Samsung Galaxy S21 is in the third house.
    s.add(pos_phone["samsung galaxy s21"] == 3)

    # 6. Eric is the person with a doctorate.
    s.add(pos_name["Eric"] == pos_edu["doctorate"])

    # 7. The person with a doctorate is in the third house.
    s.add(pos_edu["doctorate"] == 3)

    # 8. The person who loves stir fry is the person with a bachelor's degree.
    s.add(pos_food["stir fry"] == pos_edu["bachelor"])

    # 9. The person with a doctorate is the person who is a pizza lover.
    s.add(pos_edu["doctorate"] == pos_food["pizza"])

    # 10. The person whose favorite color is green is somewhere to the right of Peter.
    s.add(pos_color["green"] > pos_name["Peter"])

    # 11. The person who enjoys camping trips is the person who uses an iPhone 13.
    s.add(pos_vac["camping"] == pos_phone["iphone 13"])

    # 12. The person who likes going on cruises is Alice.
    s.add(pos_vac["cruise"] == pos_name["Alice"])

    # 13. There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
    s.add(diff_eq(pos_edu["high school"], pos_phone["samsung galaxy s21"], 2))

    # 14. The person who uses a Google Pixel 6 is Arnold.
    s.add(pos_phone["google pixel 6"] == pos_name["Arnold"])

    # 15. The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
    s.add(pos_phone["oneplus 9"] > pos_phone["huawei p50"])

    # 16. Arnold is the person who loves eating grilled cheese.
    s.add(pos_name["Arnold"] == pos_food["grilled cheese"])

    # 17. The person who loves eating grilled cheese is not in the fourth house.
    s.add(pos_food["grilled cheese"] != 4)

    # 18. There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
    s.add(diff_eq(pos_edu["bachelor"], pos_color["red"], 3))

    # 19. The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
    s.add(pos_vac["beach"] > pos_vac["city"])

    # 20. The person whose favorite color is green is not in the second house.
    s.add(pos_color["green"] != 2)

    # 21. The person who loves blue is somewhere to the right of Peter.
    s.add(pos_color["blue"] > pos_name["Peter"])

    # 22. There is one house between the person who enjoys camping trips and the person who loves yellow.
    s.add(diff_eq(pos_vac["camping"], pos_color["yellow"], 2))

    assert s.check() == sat
    m = s.model()

    # Build reverse mappings from position to value
    def invert(mapping):
        inv = {}
        for k, v in mapping.items():
            inv[m[v].as_long()] = k
        return inv

    inv_name = invert(pos_name)
    inv_vac = invert(pos_vac)
    inv_edu = invert(pos_edu)
    inv_color = invert(pos_color)
    inv_phone = invert(pos_phone)
    inv_food = invert(pos_food)

    rows = []
    for h in houses:
        row = [
            str(h),
            inv_name[h],
            inv_vac[h],
            inv_edu[h],
            inv_color[h],
            inv_phone[h],
            inv_food[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()