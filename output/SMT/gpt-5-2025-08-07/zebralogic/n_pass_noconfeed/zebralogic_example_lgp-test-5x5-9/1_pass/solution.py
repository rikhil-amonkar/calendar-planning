import json
from z3 import Solver, Int, Distinct, And, Abs, sat

def make_vars(items, prefix):
    vars_map = {}
    for it in items:
        vname = f"{prefix}_{it.replace(' ', '_')}"
        vars_map[it] = Int(vname)
    return vars_map

def all_different_in_range(s, vars_map, lo=1, hi=5):
    vals = list(vars_map.values())
    s.add(Distinct(vals))
    for v in vals:
        s.add(And(v >= lo, v <= hi))

def invert_mapping(model, pos_map):
    # Returns a list index by house-1 -> item
    house_to_item = [""] * 5
    for item, var in pos_map.items():
        h = model[var].as_long()
        house_to_item[h-1] = item
    return house_to_item

def main():
    # Enumerations
    names = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
    drinks = ["milk", "root beer", "coffee", "tea", "water"]
    colors = ["blue", "green", "white", "yellow", "red"]
    flowers = ["daffodils", "roses", "lilies", "tulips", "carnations"]
    hobbies = ["painting", "cooking", "photography", "gardening", "knitting"]

    # Create position variables for each item (house position 1..5)
    pos_name = make_vars(names, "pos_name")
    pos_drink = make_vars(drinks, "pos_drink")
    pos_color = make_vars(colors, "pos_color")
    pos_flower = make_vars(flowers, "pos_flower")
    pos_hobby = make_vars(hobbies, "pos_hobby")

    s = Solver()

    # All-different and range constraints
    all_different_in_range(s, pos_name)
    all_different_in_range(s, pos_drink)
    all_different_in_range(s, pos_color)
    all_different_in_range(s, pos_flower)
    all_different_in_range(s, pos_hobby)

    # Clues
    # 1. Alice is not in the fourth house.
    s.add(pos_name["Alice"] != 4)
    # 2. The root beer lover is the person who enjoys gardening.
    s.add(pos_drink["root beer"] == pos_hobby["gardening"])
    # 3. The person whose favorite color is green is the coffee drinker.
    s.add(pos_color["green"] == pos_drink["coffee"])
    # 4. The person whose favorite color is green is the person who loves the boquet of lilies.
    s.add(pos_color["green"] == pos_flower["lilies"])
    # 5. The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils.
    s.add(pos_color["blue"] > pos_flower["daffodils"])
    # 6. The person who loves cooking is the person who loves blue.
    s.add(pos_hobby["cooking"] == pos_color["blue"])
    # 7. Eric is directly left of the tea drinker.
    s.add(pos_name["Eric"] + 1 == pos_drink["tea"])
    # 8. The one who only drinks water is Peter.
    s.add(pos_drink["water"] == pos_name["Peter"])
    # 9. Arnold is the photography enthusiast.
    s.add(pos_name["Arnold"] == pos_hobby["photography"])
    # 10. The person who loves white is the person who loves the rose bouquet.
    s.add(pos_color["white"] == pos_flower["roses"])
    # 11. There is one house between the person who loves a carnations arrangement and the person whose favorite color is red.
    s.add(Abs(pos_flower["carnations"] - pos_color["red"]) == 2)
    # 12. The person who loves cooking is somewhere to the left of the person who paints as a hobby.
    s.add(pos_hobby["cooking"] < pos_hobby["painting"])
    # 13. The one who only drinks water is in the third house.
    s.add(pos_drink["water"] == 3)
    # 14. The person who loves a carnations arrangement is the root beer lover.
    s.add(pos_flower["carnations"] == pos_drink["root beer"])
    # 15. The person who loves white is in the second house.
    s.add(pos_color["white"] == 2)

    assert s.check() == sat
    m = s.model()

    # Invert mappings to get house -> attributes
    house_to_name = invert_mapping(m, pos_name)
    house_to_drink = invert_mapping(m, pos_drink)
    house_to_color = invert_mapping(m, pos_color)
    house_to_flower = invert_mapping(m, pos_flower)
    house_to_hobby = invert_mapping(m, pos_hobby)

    rows = []
    for h in range(1, 6):
        row = [
            str(h),
            house_to_name[h-1],
            house_to_drink[h-1],
            house_to_color[h-1],
            house_to_flower[h-1],
            house_to_hobby[h-1],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()