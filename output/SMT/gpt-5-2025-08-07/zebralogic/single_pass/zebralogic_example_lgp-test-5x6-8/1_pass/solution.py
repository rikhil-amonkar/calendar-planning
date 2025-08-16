import json
from z3 import Solver, Int, Distinct, And, Or

def solve_puzzle():
    houses = range(1, 6)

    # Categories and values
    Names = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
    HouseStyles = ["modern", "craftsman", "ranch", "victorian", "colonial"]
    Mothers = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
    Phones = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
    Drinks = ["coffee", "water", "root beer", "tea", "milk"]
    Animals = ["fish", "dog", "horse", "bird", "cat"]

    # Helper to create Z3 Int vars for each value in a category
    def mk_vars(prefix, values):
        return {v: Int(f"{prefix}_{v.replace(' ', '_').replace('-', '_')}") for v in values}

    pos_name = mk_vars("Name", Names)
    pos_style = mk_vars("Style", HouseStyles)
    pos_mother = mk_vars("Mother", Mothers)
    pos_phone = mk_vars("Phone", Phones)
    pos_drink = mk_vars("Drink", Drinks)
    pos_animal = mk_vars("Animal", Animals)

    s = Solver()

    # Domain constraints: each value is assigned a house 1..5, and all values in a category are in distinct houses
    def add_domain_and_distinct(d):
        for v in d.values():
            s.add(And(v >= 1, v <= 5))
        s.add(Distinct(list(d.values())))

    for d in [pos_name, pos_style, pos_mother, pos_phone, pos_drink, pos_animal]:
        add_domain_and_distinct(d)

    # Shorthands
    N = pos_name
    S = pos_style
    M = pos_mother
    P = pos_phone
    D = pos_drink
    A = pos_animal

    # Clues encoding

    # 1. The person who uses a Google Pixel 6 is not in the first house.
    s.add(P["google pixel 6"] != 1)

    # 2. The one who only drinks water is Alice.
    s.add(D["water"] == N["Alice"])

    # 3. The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
    s.add(S["colonial"] > P["huawei p50"])

    # 4. The person who keeps horses is the person who uses a OnePlus 9.
    s.add(A["horse"] == P["oneplus 9"])

    # 5. The person in a ranch-style home is The person whose mother's name is Kailyn.
    s.add(S["ranch"] == M["Kailyn"])

    # 6. The root beer lover is the cat lover.
    s.add(D["root beer"] == A["cat"])

    # 7. The person living in a colonial-style house is not in the fourth house.
    s.add(S["colonial"] != 4)

    # 8. The bird keeper is in the fourth house.
    s.add(A["bird"] == 4)

    # 9. The tea drinker is Bob.
    s.add(D["tea"] == N["Bob"])

    # 10. The tea drinker is somewhere to the right of The person whose mother's name is Kailyn.
    s.add(D["tea"] > M["Kailyn"])

    # 11. The root beer lover is somewhere to the left of The person whose mother's name is Kailyn.
    s.add(D["root beer"] < M["Kailyn"])

    # 12. The person who keeps horses is the person in a modern-style house.
    s.add(A["horse"] == S["modern"])

    # 13. The person who uses an iPhone 13 is the person who likes milk.
    s.add(P["iphone 13"] == D["milk"])

    # 14. The dog owner is the person who likes milk.
    s.add(A["dog"] == D["milk"])

    # 15. The person who uses a Google Pixel 6 is the person in a Craftsman-style house.
    s.add(P["google pixel 6"] == S["craftsman"])

    # 16. Eric is not in the second house.
    s.add(N["Eric"] != 2)

    # 17. The tea drinker is in the fourth house.
    s.add(D["tea"] == 4)

    # 18. The person who keeps horses is in the third house.
    s.add(A["horse"] == 3)

    # 19. The person in a modern-style house is The person whose mother's name is Penny.
    s.add(S["modern"] == M["Penny"])

    # 20. The root beer lover is Peter.
    s.add(D["root beer"] == N["Peter"])

    # 21. The person whose mother's name is Aniya is not in the fourth house.
    s.add(M["Aniya"] != 4)

    # 22. The person whose mother's name is Janelle is the one who only drinks water.
    s.add(M["Janelle"] == D["water"])

    # Solve
    if s.check() != 1:  # sat == 1
        raise RuntimeError("No solution found")

    m = s.model()

    # Build inverse maps: for each house index, get the category value
    def invert_mapping(d):
        inv = {}
        for k, v in d.items():
            inv[m[v].as_long()] = k
        return inv

    inv_name = invert_mapping(pos_name)
    inv_style = invert_mapping(pos_style)
    inv_mother = invert_mapping(pos_mother)
    inv_phone = invert_mapping(pos_phone)
    inv_drink = invert_mapping(pos_drink)
    inv_animal = invert_mapping(pos_animal)

    header = ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            inv_name[h],
            inv_style[h],
            inv_mother[h],
            inv_phone[h],
            inv_drink[h],
            inv_animal[h],
        ])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result


if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))