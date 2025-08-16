from z3 import Solver, Int, Distinct, Or
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    # Categories
    Names = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    Vacations = ["cruise", "city", "camping", "beach", "mountain"]
    Children = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    Nationalities = ["dane", "norwegian", "brit", "german", "swede"]

    # Variables: each attribute maps to a house number 1..5
    name_vars = {n: Int(f"name_{n}") for n in Names}
    vac_vars = {v: Int(f"vac_{v}") for v in Vacations}
    child_vars = {c: Int(f"child_{c}") for c in Children}
    nat_vars = {n: Int(f"nat_{n}") for n in Nationalities}

    s = Solver()

    # Domain constraints
    for v in list(name_vars.values()) + list(vac_vars.values()) + list(child_vars.values()) + list(nat_vars.values()):
        s.add(v >= 1, v <= 5)

    # All-different within each category
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*vac_vars.values()))
    s.add(Distinct(*child_vars.values()))
    s.add(Distinct(*nat_vars.values()))

    # Clues:
    # 1. The Norwegian is Peter.
    s.add(nat_vars["norwegian"] == name_vars["Peter"])

    # 2. The Swedish person is the person's child is named Bella.
    s.add(nat_vars["swede"] == child_vars["Bella"])

    # 3. The person who loves beach vacations is directly left of the person's child is named Samantha.
    s.add(vac_vars["beach"] + 1 == child_vars["Samantha"])

    # 4. The person's child is named Bella is not in the second house.
    s.add(child_vars["Bella"] != 2)

    # 5. Alice is the British person.
    s.add(name_vars["Alice"] == nat_vars["brit"])

    # 6. The person who likes going on cruises is in the first house.
    s.add(vac_vars["cruise"] == 1)

    # 7. The person's child is named Meredith is in the fourth house.
    s.add(child_vars["Meredith"] == 4)

    # 8. Eric is not in the fifth house.
    s.add(name_vars["Eric"] != 5)

    # 9. The Swedish person is somewhere to the right of the Norwegian.
    s.add(nat_vars["swede"] > nat_vars["norwegian"])

    # 10. There is one house between the person's child is named Fred and the person who prefers city breaks.
    s.add(Or(child_vars["Fred"] == vac_vars["city"] + 2,
             child_vars["Fred"] == vac_vars["city"] - 2))

    # 11. Bob is the person who enjoys camping trips.
    s.add(name_vars["Bob"] == vac_vars["camping"])

    # 12. The Dane is in the fifth house.
    s.add(nat_vars["dane"] == 5)

    # 13. The person who enjoys camping trips is not in the fifth house.
    s.add(vac_vars["camping"] != 5)

    assert s.check().r == 1, "Puzzle is unsatisfiable"
    m = s.model()

    # Helper to invert mapping from attribute->house to house->attribute
    def invert(mapping):
        inv = {}
        for k, v in mapping.items():
            inv[m[v].as_long()] = k
        return inv

    names_by_house = invert(name_vars)
    vac_by_house = invert(vac_vars)
    child_by_house = invert(child_vars)
    nat_by_house = invert(nat_vars)

    # Build JSON result
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": []
        }
    }

    for h in houses:
        row = [
            str(h),
            names_by_house[h],
            vac_by_house[h],
            child_by_house[h],
            nat_by_house[h],
        ]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()