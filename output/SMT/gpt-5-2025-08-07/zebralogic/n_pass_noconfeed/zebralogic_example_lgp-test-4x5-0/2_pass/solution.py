import json
from z3 import Solver, Int, Distinct, And, Or, sat

def create_category(vars_list, prefix):
    vars_map = {name: Int(f"{prefix}_{name.replace(' ', '_')}") for name in vars_list}
    return vars_map

def all_in_range(vars_map, low, high):
    return [And(v >= low, v <= high) for v in vars_map.values()]

def invert_mapping(model, vars_map):
    inv = {}
    for label, var in vars_map.items():
        inv[model.evaluate(var).as_long()] = label
    return inv

def main():
    houses = [1, 2, 3, 4]

    # Categories
    Names = ["Eric", "Peter", "Arnold", "Alice"]
    Smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    Cigars = ["blue master", "pall mall", "dunhill", "prince"]
    Heights = ["tall", "average", "short", "very short"]
    Phones = ["google pixel 6", "samsung galaxy s21", "iphone 13", "oneplus 9"]

    name = create_category(Names, "name")
    smoothie = create_category(Smoothies, "smoothie")
    cigar = create_category(Cigars, "cigar")
    height = create_category(Heights, "height")
    phone = create_category(Phones, "phone")

    s = Solver()

    # All different within each category and range constraints
    s.add(Distinct(list(name.values())))
    s.add(Distinct(list(smoothie.values())))
    s.add(Distinct(list(cigar.values())))
    s.add(Distinct(list(height.values())))
    s.add(Distinct(list(phone.values())))

    s.add(*all_in_range(name, 1, 4))
    s.add(*all_in_range(smoothie, 1, 4))
    s.add(*all_in_range(cigar, 1, 4))
    s.add(*all_in_range(height, 1, 4))
    s.add(*all_in_range(phone, 1, 4))

    # Clues:

    # 1. The Dragonfruit smoothie lover is Eric.
    s.add(smoothie["dragonfruit"] == name["Eric"])

    # 2. The Dunhill smoker is the person who likes Cherry smoothies.
    s.add(cigar["dunhill"] == smoothie["cherry"])

    # 3. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    s.add(phone["samsung galaxy s21"] + 1 == phone["iphone 13"])

    # 4. The Dunhill smoker is somewhere to the right of the person who is very short.
    s.add(cigar["dunhill"] > height["very short"])

    # 5. The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    s.add(smoothie["watermelon"] > smoothie["desert"])

    # 6. The Prince smoker is the person who uses a OnePlus 9.
    s.add(cigar["prince"] == phone["oneplus 9"])

    # 7. The person who is tall is in the third house.
    s.add(height["tall"] == 3)

    # 8. The person who is very short is the person who uses an iPhone 13.
    s.add(height["very short"] == phone["iphone 13"])

    # 9. The person who smokes Blue Master is not in the first house.
    s.add(cigar["blue master"] != 1)

    # 10. The Dunhill smoker is the person who is short.
    s.add(cigar["dunhill"] == height["short"])

    # 11. Peter is not in the third house.
    s.add(name["Peter"] != 3)

    # 12. Arnold is the person who uses a Google Pixel 6.
    s.add(name["Arnold"] == phone["google pixel 6"])

    # 13. The Dragonfruit smoothie lover is the person partial to Pall Mall.
    s.add(smoothie["dragonfruit"] == cigar["pall mall"])

    if s.check() != sat:
        # In case of unsatisfiable (should not happen), output empty rows but valid JSON structure
        output = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                "rows": []
            }
        }
        print(json.dumps(output, ensure_ascii=False))
        return

    m = s.model()

    inv_name = invert_mapping(m, name)
    inv_smoothie = invert_mapping(m, smoothie)
    inv_cigar = invert_mapping(m, cigar)
    inv_height = invert_mapping(m, height)
    inv_phone = invert_mapping(m, phone)

    rows = []
    for h in houses:
        row = [
            str(h),
            inv_name[h],
            inv_smoothie[h],
            inv_cigar[h],
            inv_height[h],
            inv_phone[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()