import json
from z3 import *

def solve_puzzle():
    # Define domains
    houses = range(5)  # 0..4 represent houses 1..5

    Names = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    Vacations = ["cruise", "city", "camping", "beach", "mountain"]
    Children = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    Nationalities = ["dane", "norwegian", "brit", "german", "swede"]

    # Helper to create position variables for each category
    def make_positions(prefix, labels):
        return {label: Int(f"pos_{prefix}_{label}") for label in labels}

    pos_name = make_positions("name", Names)
    pos_vac = make_positions("vac", Vacations)
    pos_child = make_positions("child", Children)
    pos_nat = make_positions("nat", Nationalities)

    s = Solver()

    # Range constraints
    for d in [pos_name, pos_vac, pos_child, pos_nat]:
        for v in d.values():
            s.add(v >= 0, v <= 4)

    # AllDifferent within each category
    s.add(Distinct([pos_name[n] for n in Names]))
    s.add(Distinct([pos_vac[v] for v in Vacations]))
    s.add(Distinct([pos_child[c] for c in Children]))
    s.add(Distinct([pos_nat[t] for t in Nationalities]))

    # Clues:

    # 1. The Norwegian is Peter.
    s.add(pos_name["Peter"] == pos_nat["norwegian"])

    # 2. The Swedish person is the person's child is named Bella.
    s.add(pos_nat["swede"] == pos_child["Bella"])

    # 3. The person who loves beach vacations is directly left of the person's child is named Samantha.
    s.add(pos_vac["beach"] + 1 == pos_child["Samantha"])

    # 4. The person's child is named Bella is not in the second house.
    s.add(pos_child["Bella"] != 1)

    # 5. Alice is the British person.
    s.add(pos_name["Alice"] == pos_nat["brit"])

    # 6. The person who likes going on cruises is in the first house.
    s.add(pos_vac["cruise"] == 0)

    # 7. The person's child is named Meredith is in the fourth house.
    s.add(pos_child["Meredith"] == 3)

    # 8. Eric is not in the fifth house.
    s.add(pos_name["Eric"] != 4)

    # 9. The Swedish person is somewhere to the right of the Norwegian.
    s.add(pos_nat["swede"] > pos_nat["norwegian"])

    # 10. There is one house between the person's child is named Fred and the person who prefers city breaks.
    s.add(Or(pos_child["Fred"] == pos_vac["city"] + 2,
             pos_child["Fred"] == pos_vac["city"] - 2))

    # 11. Bob is the person who enjoys camping trips.
    s.add(pos_name["Bob"] == pos_vac["camping"])

    # 12. The Dane is in the fifth house.
    s.add(pos_nat["dane"] == 4)

    # 13. The person who enjoys camping trips is not in the fifth house.
    s.add(pos_vac["camping"] != 4)

    if s.check() != sat:
        # In case of inconsistency, return an empty structured JSON
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                "rows": []
            }
        }
        return result

    m = s.model()

    # Invert mappings for output per house
    def invert(pos_map):
        inv = {}
        for k, v in pos_map.items():
            inv[m.eval(v).as_long()] = k
        return inv

    inv_name = invert(pos_name)
    inv_vac = invert(pos_vac)
    inv_child = invert(pos_child)
    inv_nat = invert(pos_nat)

    rows = []
    for h in houses:
        row = [
            str(h + 1),
            inv_name[h],
            inv_vac[h],
            inv_child[h],
            inv_nat[h]
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))