import json
from z3 import Solver, Int, And, Distinct, sat

def make_category_vars(prefix, values, house_min=1, house_max=4):
    vars_dict = {v: Int(f"{prefix}_{v}") for v in values}
    domain_constraints = [And(vars_dict[v] >= house_min, vars_dict[v] <= house_max) for v in values]
    return vars_dict, domain_constraints

def add_all_different(s, vars_dict):
    s.add(Distinct(list(vars_dict.values())))

def value_for_house(model, vars_dict, house):
    for k, v in vars_dict.items():
        if model.eval(v).as_long() == house:
            return k
    return None

def main():
    houses = [1, 2, 3, 4]

    Names = ["Peter", "Arnold", "Eric", "Alice"]
    Flowers = ["daffodils", "carnations", "roses", "lilies"]
    Heights = ["very short", "short", "tall", "average"]
    Mothers = ["Janelle", "Kailyn", "Holly", "Aniya"]
    Occupations = ["engineer", "doctor", "teacher", "artist"]
    Sports = ["swimming", "basketball", "tennis", "soccer"]

    s = Solver()

    name_vars, name_dom = make_category_vars("Name", Names)
    flower_vars, flower_dom = make_category_vars("Flower", Flowers)
    height_vars, height_dom = make_category_vars("Height", Heights)
    mother_vars, mother_dom = make_category_vars("Mother", Mothers)
    occupation_vars, occupation_dom = make_category_vars("Occupation", Occupations)
    sport_vars, sport_dom = make_category_vars("Sport", Sports)

    # Add domain constraints
    for dom in [name_dom, flower_dom, height_dom, mother_dom, occupation_dom, sport_dom]:
        s.add(dom)

    # All-different within each category
    add_all_different(s, name_vars)
    add_all_different(s, flower_vars)
    add_all_different(s, height_vars)
    add_all_different(s, mother_vars)
    add_all_different(s, occupation_vars)
    add_all_different(s, sport_vars)

    # Clues:
    # 1. The person who loves swimming is the person who loves the rose bouquet.
    s.add(sport_vars["swimming"] == flower_vars["roses"])

    # 2. The person who loves the rose bouquet is Eric.
    s.add(name_vars["Eric"] == flower_vars["roses"])

    # 3. Arnold is the person who is tall.
    s.add(name_vars["Arnold"] == height_vars["tall"])

    # 4. The person who loves a bouquet of daffodils is somewhere to the right of the person who is an engineer.
    s.add(flower_vars["daffodils"] > occupation_vars["engineer"])

    # 5. The person who loves soccer is the person who is short.
    s.add(sport_vars["soccer"] == height_vars["short"])

    # 6. The person who is a teacher is in the first house.
    s.add(occupation_vars["teacher"] == 1)

    # 7. The person whose mother's name is Janelle is the person who loves a carnations arrangement.
    s.add(mother_vars["Janelle"] == flower_vars["carnations"])

    # 8. The person who loves basketball is the person who has an average height.
    s.add(sport_vars["basketball"] == height_vars["average"])

    # 9. Arnold is not in the third house.
    s.add(name_vars["Arnold"] != 3)

    # 10. The person whose mother's name is Holly is somewhere to the right of the person who has an average height.
    s.add(mother_vars["Holly"] > height_vars["average"])

    # 11. Peter is the person who is a doctor.
    s.add(name_vars["Peter"] == occupation_vars["doctor"])

    # 12. The person whose mother's name is Aniya is Alice.
    s.add(mother_vars["Aniya"] == name_vars["Alice"])

    # 13. Arnold is the person who loves the boquet of lilies.
    s.add(name_vars["Arnold"] == flower_vars["lilies"])

    if s.check() != sat:
        raise ValueError("No solution found")

    m = s.model()

    header = ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"]
    rows = []
    for h in houses:
        row = [
            str(h),
            value_for_house(m, name_vars, h),
            value_for_house(m, flower_vars, h),
            value_for_house(m, height_vars, h),
            value_for_house(m, mother_vars, h),
            value_for_house(m, occupation_vars, h),
            value_for_house(m, sport_vars, h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()