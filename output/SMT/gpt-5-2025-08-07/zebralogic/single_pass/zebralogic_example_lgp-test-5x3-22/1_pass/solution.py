import json
from z3 import Int, Solver, Distinct, Or, sat

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities = ["german", "swede", "norwegian", "dane", "brit"]

    # Variables: position (house number 1..5) for each attribute value
    name_pos = {n: Int(f"name_{n}") for n in names}
    smoothie_pos = {s: Int(f"smoothie_{s}") for s in smoothies}
    nat_pos = {n: Int(f"nat_{n}") for n in nationalities}

    s = Solver()

    # Domains
    for v in list(name_pos.values()) + list(smoothie_pos.values()) + list(nat_pos.values()):
        s.add(v >= 1, v <= 5)

    # All-different within each category
    s.add(Distinct(*name_pos.values()))
    s.add(Distinct(*smoothie_pos.values()))
    s.add(Distinct(*nat_pos.values()))

    # Clues:
    # 1. Dragonfruit left of Eric
    s.add(smoothie_pos["dragonfruit"] < name_pos["Eric"])

    # 2. Dragonfruit in the second house
    s.add(smoothie_pos["dragonfruit"] == 2)

    # 3. Peter is not in the first house
    s.add(name_pos["Peter"] != 1)

    # 4. Dane and Brit are next to each other
    s.add(Or(nat_pos["dane"] - nat_pos["brit"] == 1, nat_pos["brit"] - nat_pos["dane"] == 1))

    # 5. Desert not in the fifth house
    s.add(smoothie_pos["desert"] != 5)

    # 6. Swede left of Dragonfruit
    s.add(nat_pos["swede"] < smoothie_pos["dragonfruit"])

    # 7. Two houses between Lime and Dane
    s.add(Or(smoothie_pos["lime"] - nat_pos["dane"] == 3,
             nat_pos["dane"] - smoothie_pos["lime"] == 3))

    # 8. Bob is the Dane
    s.add(name_pos["Bob"] == nat_pos["dane"])

    # 9. Alice is the Norwegian
    s.add(name_pos["Alice"] == nat_pos["norwegian"])

    # 10. Alice in the third house
    s.add(name_pos["Alice"] == 3)

    # 11. Watermelon in the third house
    s.add(smoothie_pos["watermelon"] == 3)

    assert s.check() == sat, "No solution found"
    m = s.model()

    # Build per-house assignments
    names_at = [""] * 5
    smoothies_at = [""] * 5
    nat_at = [""] * 5

    for n in names:
        names_at[m[name_pos[n]].as_long() - 1] = n
    for sm in smoothies:
        smoothies_at[m[smoothie_pos[sm]].as_long() - 1] = sm
    for nt in nationalities:
        nat_at[m[nat_pos[nt]].as_long() - 1] = nt

    # Prepare JSON structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": []
        }
    }
    for i in range(5):
        solution["solution"]["rows"].append([
            str(i + 1),
            names_at[i],
            smoothies_at[i],
            nat_at[i]
        ])

    print(json.dumps(solution, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()