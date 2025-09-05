import json
from z3 import Solver, Int, And, Or, Distinct

def main():
    n_houses = 6
    houses = list(range(1, n_houses + 1))

    # Enumerations
    names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

    # Position variables: position (1..6) of each item in its category
    pos_name = {name: Int(f"pos_name_{name}") for name in names}
    pos_child = {child: Int(f"pos_child_{child}") for child in children}
    pos_smoothie = {sm: Int(f"pos_smoothie_{sm}") for sm in smoothies}

    s = Solver()

    # Domain constraints: each position is within 1..6
    for d in [pos_name, pos_child, pos_smoothie]:
        for v in d.values():
            s.add(And(v >= 1, v <= n_houses))

    # All different constraints within each category
    s.add(Distinct([pos_name[n] for n in names]))
    s.add(Distinct([pos_child[c] for c in children]))
    s.add(Distinct([pos_smoothie[sm] for sm in smoothies]))

    # Helper to reference indices by label
    def N(x): return pos_name[x]
    def C(x): return pos_child[x]
    def S(x): return pos_smoothie[x]

    # Clues:
    # 1. The person's child is named Fred and the Desert smoothie lover are next to each other.
    s.add(Or(C("Fred") == S("desert") + 1, C("Fred") == S("desert") - 1))

    # 2. The person who drinks Blueberry smoothies is somewhere to the left of the person's child is named Fred.
    s.add(S("blueberry") < C("Fred"))

    # 3. Alice is not in the fifth house.
    s.add(N("Alice") != 5)

    # 4. The person's child is named Samantha is not in the second house.
    s.add(C("Samantha") != 2)

    # 5. The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies.
    s.add(S("watermelon") > S("cherry"))

    # 6. Alice is the person's child is named Alice. (Alice's child is Alice)
    s.add(N("Alice") == C("Alice"))

    # 7. Alice is the Watermelon smoothie lover.
    s.add(N("Alice") == S("watermelon"))

    # 8. Peter is somewhere to the right of the person's child is named Samantha.
    s.add(N("Peter") > C("Samantha"))

    # 9. Arnold is not in the second house.
    s.add(N("Arnold") != 2)

    # 10. Bob is the person who is the mother of Timothy.
    s.add(N("Bob") == C("Timothy"))

    # 11. Arnold is directly left of Carol.
    s.add(N("Arnold") + 1 == N("Carol"))

    # 12. The person who likes Cherry smoothies is directly left of the person's child is named Samantha.
    s.add(S("cherry") + 1 == C("Samantha"))

    # 13. The person's child is named Meredith is in the sixth house.
    s.add(C("Meredith") == 6)

    # 14. The Dragonfruit smoothie lover is the person's child is named Meredith.
    s.add(S("dragonfruit") == C("Meredith"))

    assert s.check().r == 1, "Puzzle is unsatisfiable"

    m = s.model()

    # Build inverse maps from position to item
    def invert_position_map(pos_vars, items):
        inv = {}
        for item in items:
            inv[int(str(m.eval(pos_vars[item])))] = item
        return inv

    name_at_pos = invert_position_map(pos_name, names)
    child_at_pos = invert_position_map(pos_child, children)
    smoothie_at_pos = invert_position_map(pos_smoothie, smoothies)

    rows = []
    for h in houses:
        rows.append([str(h), name_at_pos[h], child_at_pos[h], smoothie_at_pos[h]])

    output = {
        "solution": {
            "header": ["House", "Name", "Children", "Smoothie"],
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()