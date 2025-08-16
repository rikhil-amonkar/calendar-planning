import json
from z3 import Int, Solver, Distinct, Or, And

def solve():
    # Houses indexed 0..4 (representing houses 1..5 from left to right)
    houses = list(range(5))

    # Attribute domains
    Names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
    Heights = ['average', 'very tall', 'very short', 'short', 'tall']
    Cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
    Smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
    Phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

    # Maps from attribute value to Z3 Int var representing its house position (0..4)
    name_pos = {n: Int(f"name_{n}") for n in Names}
    height_pos = {h: Int(f"height_{h.replace(' ', '_')}") for h in Heights}
    cigar_pos = {c: Int(f"cigar_{c.replace(' ', '_')}") for c in Cigars}
    smoothie_pos = {s: Int(f"smoothie_{s.replace(' ', '_')}") for s in Smoothies}
    phone_pos = {p: Int(f"phone_{p.replace(' ', '_')}") for p in Phones}

    s = Solver()

    # Domain constraints: each attribute position is between 0 and 4
    for d in [name_pos, height_pos, cigar_pos, smoothie_pos, phone_pos]:
        for v in d.values():
            s.add(And(v >= 0, v <= 4))
        # All different within each category
        s.add(Distinct(*d.values()))

    # Helper for absolute difference equals k using Or (no Abs needed)
    def dist_eq(var1, var2, k):
        return Or(var1 + k == var2, var2 + k == var1)

    # Clues:

    # 1. The Prince smoker is the Desert smoothie lover.
    s.add(cigar_pos['prince'] == smoothie_pos['desert'])

    # 2. There is one house between Eric and Alice.
    s.add(dist_eq(name_pos['Eric'], name_pos['Alice'], 2))

    # 3. The person who is short is the person who smokes many unique blends.
    s.add(height_pos['short'] == cigar_pos['blends'])

    # 4. The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    s.add(phone_pos['iphone 13'] + 1 == cigar_pos['blue master'])

    # 5. The person who has an average height is the Dunhill smoker.
    s.add(height_pos['average'] == cigar_pos['dunhill'])

    # 6. Eric is the person who is very tall.
    s.add(name_pos['Eric'] == height_pos['very tall'])

    # 7. Arnold is directly left of the person who uses a Huawei P50.
    s.add(name_pos['Arnold'] + 1 == phone_pos['huawei p50'])

    # 8. Bob is not in the fourth house. (index 3)
    s.add(name_pos['Bob'] != 3)

    # 9. Eric is directly left of the person who likes Cherry smoothies.
    s.add(name_pos['Eric'] + 1 == smoothie_pos['cherry'])

    # 10. Bob is the Dunhill smoker.
    s.add(name_pos['Bob'] == cigar_pos['dunhill'])

    # 11. The Dragonfruit smoothie lover is Bob.
    s.add(smoothie_pos['dragonfruit'] == name_pos['Bob'])

    # 12. The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    s.add(dist_eq(phone_pos['iphone 13'], phone_pos['oneplus 9'], 1))

    # 13. The person who uses a Samsung Galaxy S21 is the person who is short.
    s.add(phone_pos['samsung galaxy s21'] == height_pos['short'])

    # 14. There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
    s.add(dist_eq(height_pos['very tall'], smoothie_pos['dragonfruit'], 3))

    # 15. The person who uses an iPhone 13 is Eric.
    s.add(phone_pos['iphone 13'] == name_pos['Eric'])

    # 16. The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    s.add(smoothie_pos['desert'] < smoothie_pos['lime'])

    # 17. Arnold and the person who is very short are next to each other.
    s.add(dist_eq(name_pos['Arnold'], height_pos['very short'], 1))

    if s.check() != 1:  # 1 stands for sat in z3py
        raise RuntimeError("No solution found")

    m = s.model()

    # Build house-wise attributes by inverting the pos maps
    house_name = [''] * 5
    house_height = [''] * 5
    house_cigar = [''] * 5
    house_smoothie = [''] * 5
    house_phone = [''] * 5

    for n, v in name_pos.items():
        house_name[m[v].as_long()] = n
    for h, v in height_pos.items():
        house_height[m[v].as_long()] = h
    for c, v in cigar_pos.items():
        house_cigar[m[v].as_long()] = c
    for sm, v in smoothie_pos.items():
        house_smoothie[m[v].as_long()] = sm
    for p, v in phone_pos.items():
        house_phone[m[v].as_long()] = p

    # Prepare JSON output
    rows = []
    for i in range(5):
        rows.append([
            str(i + 1),
            house_name[i],
            house_height[i],
            house_cigar[i],
            house_smoothie[i],
            house_phone[i]
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
            "rows": rows
        }
    }

    return result

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, ensure_ascii=False, indent=2))