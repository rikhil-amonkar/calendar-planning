import json
from z3 import Solver, Int, And, Or, Distinct

def main():
    # Domains
    houses = range(1, 6)

    Names = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
    Hobbies = ["cooking", "gardening", "painting", "photography", "knitting"]
    Sports = ["swimming", "tennis", "soccer", "baseball", "basketball"]
    HouseStyles = ["ranch", "craftsman", "victorian", "modern", "colonial"]
    Children = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
    Heights = ["average", "very tall", "very short", "short", "tall"]

    # Position variables for each attribute value (maps attribute value -> house number 1..5)
    pos_name = {n: Int(f"Name_{n}") for n in Names}
    pos_hobby = {h: Int(f"Hobby_{h}") for h in Hobbies}
    pos_sport = {s: Int(f"Sport_{s}") for s in Sports}
    pos_style = {st: Int(f"Style_{st}") for st in HouseStyles}
    pos_child = {c: Int(f"Child_{c}") for c in Children}
    pos_height = {h: Int(f"Height_{h}") for h in Heights}

    s = Solver()

    # All variables within house domain
    for d in [pos_name, pos_hobby, pos_sport, pos_style, pos_child, pos_height]:
        for v in d.values():
            s.add(And(v >= 1, v <= 5))

    # AllDifferent for each category
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_hobby.values()))
    s.add(Distinct(*pos_sport.values()))
    s.add(Distinct(*pos_style.values()))
    s.add(Distinct(*pos_child.values()))
    s.add(Distinct(*pos_height.values()))

    # Helper for adjacency
    def adj(a, b):
        return Or(a - b == 1, b - a == 1)

    # Clues encoding
    # 1. The person who has an average height is the person's child is named Meredith.
    s.add(pos_height["average"] == pos_child["Meredith"])

    # 2. The person who is tall is in the second house.
    s.add(pos_height["tall"] == 2)

    # 3. Peter is directly left of the person residing in a Victorian house.
    s.add(pos_name["Peter"] + 1 == pos_style["victorian"])

    # 4. Alice is the person who is tall.
    s.add(pos_name["Alice"] == pos_height["tall"])

    # 5. The person who loves baseball is the person who is very tall.
    s.add(pos_sport["baseball"] == pos_height["very tall"])

    # 6. The person's child is named Meredith and the person who is the mother of Timothy are next to each other.
    s.add(adj(pos_child["Meredith"], pos_child["Timothy"]))

    # 7. Bob is the person who paints as a hobby.
    s.add(pos_name["Bob"] == pos_hobby["painting"])

    # 8. The person who enjoys gardening is in the second house.
    s.add(pos_hobby["gardening"] == 2)

    # 9. The person who is very short is somewhere to the right of Eric.
    s.add(pos_height["very short"] > pos_name["Eric"])

    # 10. The person who loves tennis is the person's child is named Samantha.
    s.add(pos_sport["tennis"] == pos_child["Samantha"])

    # 11. The person who loves soccer is not in the first house.
    s.add(pos_sport["soccer"] != 1)

    # 12. The person's child is named Samantha is the person in a modern-style house.
    s.add(pos_child["Samantha"] == pos_style["modern"])

    # 13. The person in a Craftsman-style house is the person who has an average height.
    s.add(pos_style["craftsman"] == pos_height["average"])

    # 14. The person's child is named Fred is the person residing in a Victorian house.
    s.add(pos_child["Fred"] == pos_style["victorian"])

    # 15. The person who is short is the person who loves basketball.
    s.add(pos_height["short"] == pos_sport["basketball"])

    # 16. Peter is the person who is very tall.
    s.add(pos_name["Peter"] == pos_height["very tall"])

    # 17. The person in a ranch-style home is somewhere to the left of the person who loves cooking.
    s.add(pos_style["ranch"] < pos_hobby["cooking"])

    # 18. The person who enjoys knitting and the person who enjoys gardening are next to each other.
    s.add(adj(pos_hobby["knitting"], pos_hobby["gardening"]))

    # 19. The person in a modern-style house is the person who loves cooking.
    s.add(pos_style["modern"] == pos_hobby["cooking"])

    # 20. The person residing in a Victorian house is in the fifth house.
    s.add(pos_style["victorian"] == 5)

    if s.check() != 1:  # 1 == sat
        print(json.dumps({"solution": {"header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"], "rows": []}}))
        return

    m = s.model()

    def value_at_house(mapping, i):
        for k, v in mapping.items():
            if m.evaluate(v).as_long() == i:
                return k
        return None

    rows = []
    for i in houses:
        row = [
            str(i),
            value_at_house(pos_name, i),
            value_at_house(pos_hobby, i),
            value_at_house(pos_sport, i),
            value_at_house(pos_style, i),
            value_at_house(pos_child, i),
            value_at_house(pos_height, i),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()