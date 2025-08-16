from z3 import Int, Solver, Distinct, And, Or, sat
import json

def solve():
    # Domains
    houses = range(1, 7)
    people = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    # Variables: position (house number) of each person and vacation
    pos_person = {p: Int(f"pos_{p}") for p in people}
    pos_vac = {v: Int(f"pos_{v}") for v in vacations}

    s = Solver()

    # Each position is between 1 and 6
    for v in pos_person.values():
        s.add(And(v >= 1, v <= 6))
    for v in pos_vac.values():
        s.add(And(v >= 1, v <= 6))

    # All persons are in distinct houses, all vacations are in distinct houses
    s.add(Distinct(*pos_person.values()))
    s.add(Distinct(*pos_vac.values()))

    # Clues:
    # 1. cultural left of beach
    s.add(pos_vac["cultural"] < pos_vac["beach"])

    # 2. Eric is somewhere to the right of Alice
    s.add(pos_person["Eric"] > pos_person["Alice"])

    # 3. Eric is in the second house
    s.add(pos_person["Eric"] == 2)

    # 4. cultural is in the third house
    s.add(pos_vac["cultural"] == 3)

    # 5. Bob is directly left of Arnold
    s.add(pos_person["Bob"] + 1 == pos_person["Arnold"])

    # 6. camping not in the first house
    s.add(pos_vac["camping"] != 1)

    # 7. cultural is Peter
    s.add(pos_vac["cultural"] == pos_person["Peter"])

    # 8. cruises is Bob
    s.add(pos_vac["cruise"] == pos_person["Bob"])

    # 9. city in the fourth house
    s.add(pos_vac["city"] == 4)

    assert s.check() == sat
    m = s.model()

    # Build inverse mappings: house -> name, house -> vacation
    house_to_name = {m.evaluate(pos_person[p]).as_long(): p for p in people}
    house_to_vac = {m.evaluate(pos_vac[v]).as_long(): v for v in vacations}

    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_vac[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    solve()