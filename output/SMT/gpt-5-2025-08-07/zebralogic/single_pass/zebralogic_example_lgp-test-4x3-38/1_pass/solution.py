import json
from z3 import Int, Solver, Distinct, And

def solve_puzzle():
    houses = range(4)  # 0..3 correspond to houses 1..4

    Names = ["Alice", "Peter", "Arnold", "Eric"]
    Mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
    Flowers = ["carnations", "roses", "lilies", "daffodils"]

    # Position variables for each attribute value (0..3)
    name_pos = {n: Int(f"name_{n}_pos") for n in Names}
    mother_pos = {m: Int(f"mother_{m}_pos") for m in Mothers}
    flower_pos = {f: Int(f"flower_{f}_pos") for f in Flowers}

    s = Solver()

    # Domain constraints: all positions are in 0..3
    for d in [name_pos, mother_pos, flower_pos]:
        for v in d.values():
            s.add(And(v >= 0, v <= 3))

    # Uniqueness within each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([mother_pos[m] for m in Mothers]))
    s.add(Distinct([flower_pos[f] for f in Flowers]))

    # Clues:
    # 1. Alice is the person whose mother's name is Kailyn.
    s.add(name_pos["Alice"] == mother_pos["Kailyn"])

    # 2. The person whose mother's name is Janelle is somewhere to the right of Arnold.
    s.add(mother_pos["Janelle"] > name_pos["Arnold"])

    # 3. Peter is somewhere to the right of the person who loves a carnations arrangement.
    s.add(name_pos["Peter"] > flower_pos["carnations"])

    # 4. Eric is the person who loves a bouquet of daffodils.
    s.add(name_pos["Eric"] == flower_pos["daffodils"])

    # 5. Arnold is the person whose mother's name is Holly.
    s.add(name_pos["Arnold"] == mother_pos["Holly"])

    # 6. The person who loves a carnations arrangement is somewhere to the right of
    #    the person whose mother's name is Holly.
    s.add(flower_pos["carnations"] > mother_pos["Holly"])

    # 7. The person who loves the bouquet of lilies is directly left of Alice.
    s.add(flower_pos["lilies"] + 1 == name_pos["Alice"])

    # 8. Alice is in the third house.
    s.add(name_pos["Alice"] == 2)  # 0-based, so house 3 -> index 2

    assert s.check().r == 1, "Puzzle is unsatisfiable"
    m = s.model()

    # Build solution rows by house index 0..3 -> house number 1..4
    rows = []
    for i in houses:
        # Find which value occupies position i in each category
        name_at_i = next(n for n in Names if m[name_pos[n]].as_long() == i)
        mother_at_i = next(mm for mm in Mothers if m[mother_pos[mm]].as_long() == i)
        flower_at_i = next(ff for ff in Flowers if m[flower_pos[ff]].as_long() == i)

        rows.append([str(i + 1), name_at_i, mother_at_i, flower_at_i])

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Flower"],
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    solve_puzzle()