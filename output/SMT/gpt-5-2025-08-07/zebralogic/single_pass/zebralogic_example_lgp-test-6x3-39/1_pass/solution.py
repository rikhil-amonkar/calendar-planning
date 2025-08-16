from z3 import Solver, Int, And, Or, Distinct, sat
import json

def solve_puzzle():
    houses = range(1, 7)

    Names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    Children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    Smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

    # Create position variables (house index 1..6) for each attribute value
    name_pos = {n: Int(f"name_{n}") for n in Names}
    child_pos = {c: Int(f"child_{c}") for c in Children}
    smoothie_pos = {s: Int(f"smoothie_{s}") for s in Smoothies}

    s = Solver()

    # Domain constraints
    for v in list(name_pos.values()) + list(child_pos.values()) + list(smoothie_pos.values()):
        s.add(And(v >= 1, v <= 6))

    # All different in each category
    s.add(Distinct(list(name_pos.values())))
    s.add(Distinct(list(child_pos.values())))
    s.add(Distinct(list(smoothie_pos.values())))

    # Clues:
    # 1. Fred child and Desert smoothie are next to each other.
    s.add(Or(child_pos["Fred"] == smoothie_pos["desert"] + 1,
             child_pos["Fred"] == smoothie_pos["desert"] - 1))

    # 2. Blueberry is somewhere to the left of Fred (child)
    s.add(smoothie_pos["blueberry"] < child_pos["Fred"])

    # 3. Alice is not in the fifth house.
    s.add(name_pos["Alice"] != 5)

    # 4. Samantha is not in the second house.
    s.add(child_pos["Samantha"] != 2)

    # 5. Watermelon is somewhere to the right of Cherry.
    s.add(smoothie_pos["watermelon"] > smoothie_pos["cherry"])

    # 6. Alice is the person's child is named Alice. (Name Alice has child Alice)
    s.add(name_pos["Alice"] == child_pos["Alice"])

    # 7. Alice is the Watermelon smoothie lover. (Name Alice drinks Watermelon)
    s.add(name_pos["Alice"] == smoothie_pos["watermelon"])

    # 8. Peter is somewhere to the right of Samantha (child).
    s.add(name_pos["Peter"] > child_pos["Samantha"])

    # 9. Arnold is not in the second house.
    s.add(name_pos["Arnold"] != 2)

    # 10. Bob is the person who is the mother of Timothy. (Name Bob has child Timothy)
    s.add(name_pos["Bob"] == child_pos["Timothy"])

    # 11. Arnold is directly left of Carol.
    s.add(name_pos["Arnold"] + 1 == name_pos["Carol"])

    # 12. Cherry is directly left of Samantha (child).
    s.add(smoothie_pos["cherry"] + 1 == child_pos["Samantha"])

    # 13. Meredith is in the sixth house. (child Meredith at house 6)
    s.add(child_pos["Meredith"] == 6)

    # 14. Dragonfruit smoothie lover is the person's child is named Meredith. (Dragonfruit at same house as child Meredith)
    s.add(smoothie_pos["dragonfruit"] == child_pos["Meredith"])

    if s.check() != sat:
        raise ValueError("No solution found")

    m = s.model()

    # Build reverse mappings from house -> attribute value
    house_to_name = {m.eval(pos).as_long(): name for name, pos in name_pos.items()}
    house_to_child = {m.eval(pos).as_long(): child for child, pos in child_pos.items()}
    house_to_smoothie = {m.eval(pos).as_long(): sm for sm, pos in smoothie_pos.items()}

    rows = []
    for h in houses:
        rows.append([
            str(h),
            house_to_name[h],
            house_to_child[h],
            house_to_smoothie[h],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Children", "Smoothie"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()