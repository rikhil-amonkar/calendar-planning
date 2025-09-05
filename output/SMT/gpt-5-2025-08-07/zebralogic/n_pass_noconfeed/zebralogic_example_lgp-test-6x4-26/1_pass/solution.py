import json
from z3 import Int, Solver, And, Distinct, Or

def solve_puzzle():
    houses = range(1, 7)

    Names = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"]
    Pets = ["bird", "dog", "cat", "rabbit", "fish", "hamster"]
    Styles = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"]
    Birthdays = ["mar", "sept", "may", "feb", "jan", "april"]

    # Position variables for each attribute value
    pos_name = {n: Int(f"name_{n}") for n in Names}
    pos_pet = {p: Int(f"pet_{p}") for p in Pets}
    pos_style = {s: Int(f"style_{s}") for s in Styles}
    pos_bday = {b: Int(f"bday_{b}") for b in Birthdays}

    s = Solver()

    # Domain constraints: all positions between 1 and 6
    for d in [pos_name, pos_pet, pos_style, pos_bday]:
        for v in d.values():
            s.add(And(v >= 1, v <= 6))

    # Uniqueness within each category
    s.add(Distinct([pos_name[n] for n in Names]))
    s.add(Distinct([pos_pet[p] for p in Pets]))
    s.add(Distinct([pos_style[t] for t in Styles]))
    s.add(Distinct([pos_bday[m] for m in Birthdays]))

    # Helper for "exactly k houses between" -> distance = k+1
    def distance_eq(a, b, d):
        return Or(a - b == d, b - a == d)

    # Clues:
    # 1. hamster to the right of March
    s.add(pos_pet["hamster"] > pos_bday["mar"])

    # 2. January left of September
    s.add(pos_bday["jan"] < pos_bday["sept"])

    # 3. May in second house
    s.add(pos_bday["may"] == 2)

    # 4. Colonial in second house
    s.add(pos_style["colonial"] == 2)

    # 5. Carol in the third house
    s.add(pos_name["Carol"] == 3)

    # 6. Mediterranean not in the sixth house
    s.add(pos_style["mediterranean"] != 6)

    # 7. Fish to the right of Bob
    s.add(pos_pet["fish"] > pos_name["Bob"])

    # 8. Eric in the sixth house
    s.add(pos_name["Eric"] == 6)

    # 9. One house between cat and Victorian
    s.add(distance_eq(pos_pet["cat"], pos_style["victorian"], 2))

    # 10. Two houses between Victorian and hamster
    s.add(distance_eq(pos_style["victorian"], pos_pet["hamster"], 3))

    # 11. Craftsman is Arnold
    s.add(pos_style["craftsman"] == pos_name["Arnold"])

    # 12. Colonial left of modern
    s.add(pos_style["colonial"] < pos_style["modern"])

    # 13. Fish not in the second house
    s.add(pos_pet["fish"] != 2)

    # 14. Peter lives in the colonial house
    s.add(pos_name["Peter"] == pos_style["colonial"])

    # 15. January directly left of April
    s.add(pos_bday["jan"] + 1 == pos_bday["april"])

    # 16. One house between bird and modern
    s.add(distance_eq(pos_pet["bird"], pos_style["modern"], 2))

    # 17. Carol has birthday in March
    s.add(pos_name["Carol"] == pos_bday["mar"])

    # 18. Craftsman in the fourth house
    s.add(pos_style["craftsman"] == 4)

    # 19. Dog in the fourth house
    s.add(pos_pet["dog"] == 4)

    if s.check() != 1:  # sat
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Invert mappings to build per-house rows
    house_to_name = {m[pos_name[n]].as_long(): n for n in Names}
    house_to_pet = {m[pos_pet[p]].as_long(): p for p in Pets}
    house_to_style = {m[pos_style[t]].as_long(): t for t in Styles}
    house_to_bday = {m[pos_bday[b]].as_long(): b for b in Birthdays}

    result = {
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": []
        }
    }

    for h in range(1, 7):
        row = [
            str(h),
            house_to_name[h],
            house_to_pet[h],
            house_to_style[h],
            house_to_bday[h],
        ]
        result["solution"]["rows"].append(row)

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))