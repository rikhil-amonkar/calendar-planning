import json
from z3 import *

def main():
    Houses = [1, 2, 3, 4]

    # Categories and values
    names = ["Peter", "Arnold", "Alice", "Eric"]
    flowers = ["roses", "daffodils", "carnations", "lilies"]
    hobbies = ["photography", "painting", "cooking", "gardening"]
    pets = ["dog", "fish", "bird", "cat"]
    colors = ["red", "yellow", "green", "white"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]

    # Create position variables for each attribute value
    def make_pos_vars(values, prefix):
        vars_dict = {}
        for v in values:
            var = Int(f"{prefix}_{v}")
            vars_dict[v] = var
        return vars_dict

    pos_names = make_pos_vars(names, "pos_name")
    pos_flowers = make_pos_vars(flowers, "pos_flower")
    pos_hobbies = make_pos_vars(hobbies, "pos_hobby")
    pos_pets = make_pos_vars(pets, "pos_pet")
    pos_colors = make_pos_vars(colors, "pos_color")
    pos_styles = make_pos_vars(styles, "pos_style")

    s = Solver()

    # Domain constraints: All positions between 1 and 4
    def add_domain(vars_dict):
        for v in vars_dict.values():
            s.add(And(v >= 1, v <= 4))

    add_domain(pos_names)
    add_domain(pos_flowers)
    add_domain(pos_hobbies)
    add_domain(pos_pets)
    add_domain(pos_colors)
    add_domain(pos_styles)

    # All-different constraints within each category
    s.add(Distinct([pos_names[n] for n in names]))
    s.add(Distinct([pos_flowers[f] for f in flowers]))
    s.add(Distinct([pos_hobbies[h] for h in hobbies]))
    s.add(Distinct([pos_pets[p] for p in pets]))
    s.add(Distinct([pos_colors[c] for c in colors]))
    s.add(Distinct([pos_styles[st] for st in styles]))

    # Clues:
    # 1. The person in a Craftsman-style house is Arnold.
    s.add(pos_styles["craftsman"] == pos_names["Arnold"])

    # 2. The person who loves the rose bouquet is somewhere to the right of Peter.
    s.add(pos_flowers["roses"] > pos_names["Peter"])

    # 3. The photography enthusiast is the person who owns a dog.
    s.add(pos_hobbies["photography"] == pos_pets["dog"])

    # 4. The person who loves a bouquet of daffodils is not in the fourth house.
    s.add(pos_flowers["daffodils"] != 4)

    # 5. The person who loves the rose bouquet is the person whose favorite color is red.
    s.add(pos_flowers["roses"] == pos_colors["red"])

    # 6. The person in a Craftsman-style house is in the second house.
    s.add(pos_styles["craftsman"] == 2)

    # 7. Eric is the person residing in a Victorian house.
    s.add(pos_names["Eric"] == pos_styles["victorian"])

    # 8. The person with an aquarium of fish is the person who loves white.
    s.add(pos_pets["fish"] == pos_colors["white"])

    # 9. The person who loves cooking is somewhere to the right of the person whose favorite color is red.
    s.add(pos_hobbies["cooking"] > pos_colors["red"])

    # 10. The person who loves white is the person who loves a carnations arrangement.
    s.add(pos_colors["white"] == pos_flowers["carnations"])

    # 11. The person who loves white is somewhere to the right of the person who enjoys gardening.
    s.add(pos_colors["white"] > pos_hobbies["gardening"])

    # 12. The person who loves a bouquet of daffodils is the person who loves yellow.
    s.add(pos_flowers["daffodils"] == pos_colors["yellow"])

    # 13. The person living in a colonial-style house is the person whose favorite color is red.
    s.add(pos_styles["colonial"] == pos_colors["red"])

    # 14. The person who has a cat is Eric.
    s.add(pos_pets["cat"] == pos_names["Eric"])

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build inverse maps: position -> value
    def invert(vars_dict):
        inv = {}
        for k, v in vars_dict.items():
            pos = m[v].as_long()
            inv[pos] = k
        return inv

    inv_names = invert(pos_names)
    inv_flowers = invert(pos_flowers)
    inv_hobbies = invert(pos_hobbies)
    inv_pets = invert(pos_pets)
    inv_colors = invert(pos_colors)
    inv_styles = invert(pos_styles)

    rows = []
    for house in Houses:
        rows.append([
            str(house),
            inv_names[house],
            inv_flowers[house],
            inv_hobbies[house],
            inv_pets[house],
            inv_colors[house],
            inv_styles[house],
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": rows
        }
    }

    print(json.dumps(output))

if __name__ == "__main__":
    main()