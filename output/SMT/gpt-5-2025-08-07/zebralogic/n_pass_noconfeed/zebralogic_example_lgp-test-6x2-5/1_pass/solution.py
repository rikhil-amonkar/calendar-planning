import json
from z3 import *

def solve_puzzle():
    houses = range(1, 7)

    names = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    # Variables: position (house number) of each name and each vacation
    house_of_name = {name: Int(f"house_{name}") for name in names}
    house_of_vac = {vac: Int(f"house_{vac}") for vac in vacations}

    s = Solver()

    # Domains
    for v in house_of_name.values():
        s.add(And(v >= 1, v <= 6))
    for v in house_of_vac.values():
        s.add(And(v >= 1, v <= 6))

    # Uniqueness: each house has a unique name and unique vacation
    s.add(Distinct(list(house_of_name.values())))
    s.add(Distinct(list(house_of_vac.values())))

    # Clues:
    # 1. cultural left of beach
    s.add(house_of_vac["cultural"] < house_of_vac["beach"])

    # 2. Eric somewhere to the right of Alice
    s.add(house_of_name["Eric"] > house_of_name["Alice"])

    # 3. Eric is in the second house
    s.add(house_of_name["Eric"] == 2)

    # 4. cultural in the third house
    s.add(house_of_vac["cultural"] == 3)

    # 5. Bob directly left of Arnold
    s.add(house_of_name["Bob"] + 1 == house_of_name["Arnold"])

    # 6. camping not in the first house
    s.add(house_of_vac["camping"] != 1)

    # 7. cultural is Peter
    s.add(house_of_name["Peter"] == house_of_vac["cultural"])

    # 8. cruise is Bob
    s.add(house_of_name["Bob"] == house_of_vac["cruise"])

    # 9. city in the fourth house
    s.add(house_of_vac["city"] == 4)

    if s.check() != sat:
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": []
            }
        }
        print(json.dumps(result, indent=2))
        return

    m = s.model()

    # Build inverse mappings: for each house, get its name and vacation
    house_to_name = {}
    for name, var in house_of_name.items():
        house_to_name[m[var].as_long()] = name

    house_to_vac = {}
    for vac, var in house_of_vac.items():
        house_to_vac[m[var].as_long()] = vac

    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_vac[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": rows
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    solve_puzzle()