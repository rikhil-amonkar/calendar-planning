import json
from z3 import Int, Solver, And, Distinct, Abs, sat

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities = ["german", "swede", "norwegian", "dane", "brit"]

    # Position variables: position of each attribute (1..5)
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_smoothie = {s: Int(f"pos_smoothie_{s}") for s in smoothies}
    pos_nat = {na: Int(f"pos_nat_{na}") for na in nationalities}

    s = Solver()

    # Domain constraints
    for v in list(pos_name.values()) + list(pos_smoothie.values()) + list(pos_nat.values()):
        s.add(And(v >= 1, v <= 5))

    # AllDifferent constraints within each category
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_smoothie.values()))
    s.add(Distinct(*pos_nat.values()))

    # Clues:
    # 1. The Dragonfruit smoothie lover is somewhere to the left of Eric.
    s.add(pos_smoothie["dragonfruit"] < pos_name["Eric"])

    # 2. The Dragonfruit smoothie lover is in the second house.
    s.add(pos_smoothie["dragonfruit"] == 2)

    # 3. Peter is not in the first house.
    s.add(pos_name["Peter"] != 1)

    # 4. The Dane and the British person are next to each other.
    s.add(Abs(pos_nat["dane"] - pos_nat["brit"]) == 1)

    # 5. The Desert smoothie lover is not in the fifth house.
    s.add(pos_smoothie["desert"] != 5)

    # 6. The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
    s.add(pos_nat["swede"] < pos_smoothie["dragonfruit"])

    # 7. There are two houses between the person who drinks Lime smoothies and the Dane.
    s.add(Abs(pos_smoothie["lime"] - pos_nat["dane"]) == 3)

    # 8. Bob is the Dane.
    s.add(pos_name["Bob"] == pos_nat["dane"])

    # 9. Alice is the Norwegian.
    s.add(pos_name["Alice"] == pos_nat["norwegian"])

    # 10. Alice is in the third house.
    s.add(pos_name["Alice"] == 3)

    # 11. The Watermelon smoothie lover is in the third house.
    s.add(pos_smoothie["watermelon"] == 3)

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable or unknown.")

    m = s.model()

    # Build house-wise solution
    house_to_name = {}
    house_to_smoothie = {}
    house_to_nat = {}

    for h in houses:
        for n in names:
            if m.evaluate(pos_name[n]).as_long() == h:
                house_to_name[h] = n
                break
        for sm in smoothies:
            if m.evaluate(pos_smoothie[sm]).as_long() == h:
                house_to_smoothie[h] = sm
                break
        for na in nationalities:
            if m.evaluate(pos_nat[na]).as_long() == h:
                house_to_nat[h] = na
                break

    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_smoothie[h], house_to_nat[h]])

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()