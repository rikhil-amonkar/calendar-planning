import json
from z3 import *

def solve():
    houses = range(1, 7)

    # Domains
    Names = ["Eric", "Bob", "Peter", "Alice", "Arnold", "Carol"]
    Cars = ["ford f150", "honda civic", "toyota camry", "tesla model 3", "chevrolet silverado", "bmw 3 series"]
    Mothers = ["Sarah", "Penny", "Holly", "Aniya", "Kailyn", "Janelle"]
    Hobbies = ["photography", "cooking", "knitting", "gardening", "woodworking", "painting"]

    # Create Z3 Int variables mapping each value to a house position (1..6)
    def mk_vars(lst, prefix):
        return {v: Int(f"{prefix}_{v.replace(' ', '_').replace('-', '').replace('/', '')}") for v in lst}

    name_pos = mk_vars(Names, "Name")
    car_pos = mk_vars(Cars, "Car")
    mother_pos = mk_vars(Mothers, "Mother")
    hobby_pos = mk_vars(Hobbies, "Hobby")

    s = Solver()

    # Range constraints
    for d in [name_pos, car_pos, mother_pos, hobby_pos]:
        for v in d.values():
            s.add(And(v >= 1, v <= 6))

    # AllDifferent for each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([car_pos[c] for c in Cars]))
    s.add(Distinct([mother_pos[m] for m in Mothers]))
    s.add(Distinct([hobby_pos[h] for h in Hobbies]))

    # Clues:
    # 1. Toyota Camry in the sixth house.
    s.add(car_pos["toyota camry"] == 6)

    # 2. Carol is the photography enthusiast.
    s.add(name_pos["Carol"] == hobby_pos["photography"])

    # 3. Chevrolet Silverado owner is the person whose mother's name is Aniya.
    s.add(car_pos["chevrolet silverado"] == mother_pos["Aniya"])

    # 4. Chevrolet Silverado is not in the second house.
    s.add(car_pos["chevrolet silverado"] != 2)

    # 5. Ford F-150 owner is the person whose mother's name is Sarah.
    s.add(car_pos["ford f150"] == mother_pos["Sarah"])

    # 6. BMW 3 Series is Bob.
    s.add(car_pos["bmw 3 series"] == name_pos["Bob"])

    # 7. Mother's name Kailyn is in the sixth house.
    s.add(mother_pos["Kailyn"] == 6)

    # 8. Eric is directly left of the person who enjoys knitting.
    s.add(name_pos["Eric"] + 1 == hobby_pos["knitting"])

    # 9. There is one house between Sarah and Toyota Camry.
    s.add(Or(mother_pos["Sarah"] == car_pos["toyota camry"] + 2,
             mother_pos["Sarah"] == car_pos["toyota camry"] - 2))

    # 10. Penny is somewhere to the right of the person who enjoys knitting.
    s.add(mother_pos["Penny"] > hobby_pos["knitting"])

    # 11. Aniya is somewhere to the right of the Honda Civic.
    s.add(mother_pos["Aniya"] > car_pos["honda civic"])

    # 12. Alice is somewhere to the right of the Ford F-150.
    s.add(name_pos["Alice"] > car_pos["ford f150"])

    # 13. Eric is the person who enjoys gardening.
    s.add(name_pos["Eric"] == hobby_pos["gardening"])

    # 14. The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    s.add(hobby_pos["woodworking"] < hobby_pos["knitting"])

    # 15. There is one house between Sarah and the person who loves cooking.
    s.add(Or(mother_pos["Sarah"] == hobby_pos["cooking"] + 2,
             mother_pos["Sarah"] == hobby_pos["cooking"] - 2))

    # 16. The person who owns a Honda Civic is Arnold.
    s.add(car_pos["honda civic"] == name_pos["Arnold"])

    # 17. Mother's name Holly is directly left of the person who enjoys knitting.
    s.add(mother_pos["Holly"] + 1 == hobby_pos["knitting"])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    model = s.model()

    # Build reverse mappings: house -> attribute value
    def invert(dct):
        inv = {}
        for k, v in dct.items():
            inv[model[v].as_long()] = k
        return inv

    house_to_name = invert(name_pos)
    house_to_car = invert(car_pos)
    house_to_mother = invert(mother_pos)
    house_to_hobby = invert(hobby_pos)

    rows = []
    for h in houses:
        rows.append([
            str(h),
            house_to_name[h],
            house_to_car[h],
            house_to_mother[h],
            house_to_hobby[h],
        ])

    out = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
            "rows": rows
        }
    }
    print(json.dumps(out))

if __name__ == "__main__":
    solve()