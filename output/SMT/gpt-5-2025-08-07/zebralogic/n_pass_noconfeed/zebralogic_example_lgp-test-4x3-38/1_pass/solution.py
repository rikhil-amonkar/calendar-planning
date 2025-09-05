import json
from z3 import Solver, Int, Distinct, And, sat

def solve_puzzle():
    houses = [1, 2, 3, 4]

    names = ["Alice", "Peter", "Arnold", "Eric"]
    mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
    flowers = ["carnations", "roses", "lilies", "daffodils"]

    # Position variables: position of each attribute is an integer 1..4
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_mother = {m: Int(f"pos_mother_{m}") for m in mothers}
    pos_flower = {f: Int(f"pos_flower_{f}") for f in flowers}

    s = Solver()

    # Domain constraints: each position in 1..4
    for v in list(pos_name.values()) + list(pos_mother.values()) + list(pos_flower.values()):
        s.add(And(v >= 1, v <= 4))

    # Uniqueness within each category
    s.add(Distinct([pos_name[n] for n in names]))
    s.add(Distinct([pos_mother[m] for m in mothers]))
    s.add(Distinct([pos_flower[f] for f in flowers]))

    # Clues:
    # 1. Alice is The person whose mother's name is Kailyn.
    s.add(pos_name["Alice"] == pos_mother["Kailyn"])

    # 2. The person whose mother's name is Janelle is somewhere to the right of Arnold.
    s.add(pos_mother["Janelle"] > pos_name["Arnold"])

    # 3. Peter is somewhere to the right of the person who loves a carnations arrangement.
    s.add(pos_name["Peter"] > pos_flower["carnations"])

    # 4. Eric is the person who loves a bouquet of daffodils.
    s.add(pos_name["Eric"] == pos_flower["daffodils"])

    # 5. Arnold is The person whose mother's name is Holly.
    s.add(pos_name["Arnold"] == pos_mother["Holly"])

    # 6. The person who loves a carnations arrangement is somewhere to the right of
    #    The person whose mother's name is Holly.
    s.add(pos_flower["carnations"] > pos_mother["Holly"])

    # 7. The person who loves the boquet of lilies is directly left of Alice.
    s.add(pos_flower["lilies"] + 1 == pos_name["Alice"])

    # 8. Alice is in the third house.
    s.add(pos_name["Alice"] == 3)

    assert s.check() == sat, "Puzzle constraints are unsatisfiable."
    m = s.model()

    # Build inverse mappings: for each house, find the attribute at that position
    def inv_lookup(pos_map, items):
        house_to_item = {}
        for item in items:
            p = m.evaluate(pos_map[item]).as_long()
            house_to_item[p] = item
        return house_to_item

    name_at = inv_lookup(pos_name, names)
    mother_at = inv_lookup(pos_mother, mothers)
    flower_at = inv_lookup(pos_flower, flowers)

    rows = []
    for h in houses:
        rows.append([str(h), name_at[h], mother_at[h], flower_at[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Flower"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))