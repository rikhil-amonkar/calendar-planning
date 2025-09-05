import json
from z3 import Solver, Int, Distinct, If, sat

def abs_diff(a, b):
    return If(a - b >= 0, a - b, b - a)

def main():
    # Houses
    houses = [1, 2]
    N = len(houses)

    # Attributes
    Names = ["Arnold", "Eric"]
    Sports = ["basketball", "soccer"]
    HairColors = ["brown", "black"]
    Heights = ["very short", "short"]
    Smoothies = ["desert", "cherry"]
    Flowers = ["daffodils", "carnations"]

    # Helper to create Z3 variables with safe names
    def make_vars(category, values):
        return {val: Int(f"{category}_{val.replace(' ', '_')}") for val in values}

    name_pos = make_vars("Name", Names)
    sport_pos = make_vars("Sport", Sports)
    hair_pos = make_vars("Hair", HairColors)
    height_pos = make_vars("Height", Heights)
    smoothie_pos = make_vars("Smoothie", Smoothies)
    flower_pos = make_vars("Flower", Flowers)

    s = Solver()

    # Domain constraints and all-different per category
    def add_category_constraints(var_dict):
        vars_list = list(var_dict.values())
        for v in vars_list:
            s.add(v >= 1, v <= N)
        if len(vars_list) > 1:
            s.add(Distinct(vars_list))

    for d in [name_pos, sport_pos, hair_pos, height_pos, smoothie_pos, flower_pos]:
        add_category_constraints(d)

    # Clues:
    # 1. The person who loves soccer is not in the second house.
    s.add(sport_pos["soccer"] != 2)

    # 2. The Desert smoothie lover is directly left of the person who is very short.
    s.add(smoothie_pos["desert"] + 1 == height_pos["very short"])

    # 3. The person who is very short is the person who has brown hair.
    s.add(height_pos["very short"] == hair_pos["brown"])

    # 4. The person who loves a carnations arrangement is the Desert smoothie lover.
    s.add(flower_pos["carnations"] == smoothie_pos["desert"])

    # 5. Eric and the person who has brown hair are next to each other.
    s.add(abs_diff(name_pos["Eric"], hair_pos["brown"]) == 1)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Helper to invert mapping from attribute -> house
    def value_at_house(var_dict, values, house_num):
        for val in values:
            if m.evaluate(var_dict[val]).as_long() == house_num:
                return val
        return None

    header = ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"]
    rows = []
    for h in houses:
        row = [
            str(h),
            value_at_house(name_pos, Names, h),
            value_at_house(sport_pos, Sports, h),
            value_at_house(hair_pos, HairColors, h),
            value_at_house(height_pos, Heights, h),
            value_at_house(smoothie_pos, Smoothies, h),
            value_at_house(flower_pos, Flowers, h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()