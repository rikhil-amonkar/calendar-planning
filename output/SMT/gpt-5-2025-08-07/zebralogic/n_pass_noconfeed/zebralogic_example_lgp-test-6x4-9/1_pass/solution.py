import json
import re
from z3 import Solver, Int, Distinct, And, Or, Abs

def sanitize(s):
    return re.sub(r'[^A-Za-z0-9]+', '_', s)

def main():
    houses = list(range(1, 7))

    Names = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
    Phones = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
    Nationalities = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
    Colors = ["blue", "red", "yellow", "green", "white", "purple"]

    # Variables: position (house number) for each attribute value
    name_pos = {n: Int(f"pos_name_{sanitize(n)}") for n in Names}
    phone_pos = {p: Int(f"pos_phone_{sanitize(p)}") for p in Phones}
    nat_pos = {n: Int(f"pos_nat_{sanitize(n)}") for n in Nationalities}
    color_pos = {c: Int(f"pos_color_{sanitize(c)}") for c in Colors}

    s = Solver()

    # Domain constraints
    for d in (name_pos, phone_pos, nat_pos, color_pos):
        for v in d.values():
            s.add(And(v >= 1, v <= 6))

    # Uniqueness within each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([phone_pos[p] for p in Phones]))
    s.add(Distinct([nat_pos[n] for n in Nationalities]))
    s.add(Distinct([color_pos[c] for c in Colors]))

    # Clues:
    # 1. Carol is not in the third house.
    s.add(name_pos["Carol"] != 3)

    # 2. There is one house between the Dane and the British person.
    s.add(Abs(nat_pos["dane"] - nat_pos["brit"]) == 2)

    # 3. Carol is the person whose favorite color is green.
    s.add(name_pos["Carol"] == color_pos["green"])

    # 4. Arnold is directly left of Alice.
    s.add(name_pos["Arnold"] + 1 == name_pos["Alice"])

    # 5. Alice is the German.
    s.add(name_pos["Alice"] == nat_pos["german"])

    # 6. The person who uses a OnePlus 9 is the person who loves purple.
    s.add(phone_pos["oneplus 9"] == color_pos["purple"])

    # 7. The person who uses a Huawei P50 is not in the third house.
    s.add(phone_pos["huawei p50"] != 3)

    # 8. The person who uses a Samsung Galaxy S21 is in the fifth house.
    s.add(phone_pos["samsung galaxy s21"] == 5)

    # 9. The person who loves white is somewhere to the right of the person whose favorite color is red.
    s.add(color_pos["white"] > color_pos["red"])

    # 10. The person who uses a Samsung Galaxy S21 is Bob.
    s.add(phone_pos["samsung galaxy s21"] == name_pos["Bob"])

    # 11. The Dane is the person who loves yellow.
    s.add(nat_pos["dane"] == color_pos["yellow"])

    # 12. The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
    s.add(phone_pos["samsung galaxy s21"] < name_pos["Peter"])

    # 13. The person who loves blue is Peter.
    s.add(color_pos["blue"] == name_pos["Peter"])

    # 14. Peter is the British person.
    s.add(name_pos["Peter"] == nat_pos["brit"])

    # 15. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    s.add(phone_pos["samsung galaxy s21"] + 1 == phone_pos["iphone 13"])

    # 16. The Norwegian is the person who loves purple.
    s.add(nat_pos["norwegian"] == color_pos["purple"])

    # 17. The person who uses a Xiaomi Mi 11 is the Chinese.
    s.add(phone_pos["xiaomi mi 11"] == nat_pos["chinese"])

    if s.check() != 1:  # sat == 1
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    def value_at_house(pos_dict, values_list, house):
        for val in values_list:
            if m.evaluate(pos_dict[val]).as_long() == house:
                return val
        return None

    rows = []
    for h in houses:
        name = value_at_house(name_pos, Names, h)
        phone = value_at_house(phone_pos, Phones, h)
        nat = value_at_house(nat_pos, Nationalities, h)
        color = value_at_house(color_pos, Colors, h)
        rows.append([str(h), name, phone, nat, color])

    output = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()