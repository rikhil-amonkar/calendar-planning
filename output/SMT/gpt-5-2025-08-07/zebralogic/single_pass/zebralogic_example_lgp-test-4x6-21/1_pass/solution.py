import json
from z3 import Int, Solver, Distinct, And

def solve_puzzle():
    houses = range(4)  # 0..3 represent houses 1..4

    # Domains
    Names = ["Peter", "Arnold", "Alice", "Eric"]
    Flowers = ["roses", "daffodils", "carnations", "lilies"]
    Hobbies = ["photography", "painting", "cooking", "gardening"]
    Pets = ["dog", "fish", "bird", "cat"]
    Colors = ["red", "yellow", "green", "white"]
    HouseStyles = ["craftsman", "colonial", "ranch", "victorian"]

    # Create position variables for each attribute value (which house each value is in)
    pos_name = {n: Int(f"pos_name_{n}") for n in Names}
    pos_flower = {f: Int(f"pos_flower_{f}") for f in Flowers}
    pos_hobby = {h: Int(f"pos_hobby_{h}") for h in Hobbies}
    pos_pet = {p: Int(f"pos_pet_{p}") for p in Pets}
    pos_color = {c: Int(f"pos_color_{c}") for c in Colors}
    pos_style = {s: Int(f"pos_style_{s}") for s in HouseStyles}

    s = Solver()

    # Domain constraints: each position is between 0 and 3
    for d in [pos_name, pos_flower, pos_hobby, pos_pet, pos_color, pos_style]:
        for v in d.values():
            s.add(And(v >= 0, v <= 3))

    # All-different constraints within each category
    s.add(Distinct([pos_name[n] for n in Names]))
    s.add(Distinct([pos_flower[f] for f in Flowers]))
    s.add(Distinct([pos_hobby[h] for h in Hobbies]))
    s.add(Distinct([pos_pet[p] for p in Pets]))
    s.add(Distinct([pos_color[c] for c in Colors]))
    s.add(Distinct([pos_style[st] for st in HouseStyles]))

    # Clues:
    # 1. The person in a Craftsman-style house is Arnold.
    s.add(pos_style["craftsman"] == pos_name["Arnold"])

    # 2. The person who loves the rose bouquet is somewhere to the right of Peter.
    s.add(pos_flower["roses"] > pos_name["Peter"])

    # 3. The photography enthusiast is the person who owns a dog.
    s.add(pos_hobby["photography"] == pos_pet["dog"])

    # 4. The person who loves a bouquet of daffodils is not in the fourth house.
    s.add(pos_flower["daffodils"] != 3)

    # 5. The person who loves the rose bouquet is the person whose favorite color is red.
    s.add(pos_flower["roses"] == pos_color["red"])

    # 6. The person in a Craftsman-style house is in the second house.
    s.add(pos_style["craftsman"] == 1)

    # 7. Eric is the person residing in a Victorian house.
    s.add(pos_name["Eric"] == pos_style["victorian"])

    # 8. The person with an aquarium of fish is the person who loves white.
    s.add(pos_pet["fish"] == pos_color["white"])

    # 9. The person who loves cooking is somewhere to the right of the person whose favorite color is red.
    s.add(pos_hobby["cooking"] > pos_color["red"])

    # 10. The person who loves white is the person who loves a carnations arrangement.
    s.add(pos_color["white"] == pos_flower["carnations"])

    # 11. The person who loves white is somewhere to the right of the person who enjoys gardening.
    s.add(pos_color["white"] > pos_hobby["gardening"])

    # 12. The person who loves a bouquet of daffodils is the person who loves yellow.
    s.add(pos_flower["daffodils"] == pos_color["yellow"])

    # 13. The person living in a colonial-style house is the person whose favorite color is red.
    s.add(pos_style["colonial"] == pos_color["red"])

    # 14. The person who has a cat is Eric.
    s.add(pos_pet["cat"] == pos_name["Eric"])

    assert s.check() ==  sat, "No solution found"
    m = s.model()

    # Build reverse lookup: for each house index, find the value in each category
    def value_at(pos_map, values, i):
        for v in values:
            if m[pos_map[v]].as_long() == i:
                return v
        return None

    rows = []
    for i in houses:
        house_num = str(i + 1)
        name = value_at(pos_name, Names, i)
        flower = value_at(pos_flower, Flowers, i)
        hobby = value_at(pos_hobby, Hobbies, i)
        pet = value_at(pos_pet, Pets, i)
        color = value_at(pos_color, Colors, i)
        style = value_at(pos_style, HouseStyles, i)

        rows.append([house_num, name, flower, hobby, pet, color, style])

    output = {
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": rows
        }
    }

    return output

# Run and print JSON
if __name__ == "__main__":
    # z3 returns symbolic values; need 'sat' symbol
    from z3 import sat
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))