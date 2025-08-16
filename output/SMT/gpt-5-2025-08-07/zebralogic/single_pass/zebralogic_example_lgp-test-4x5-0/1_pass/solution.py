import json
from z3 import Solver, Int, Distinct

def solve_puzzle():
    # Define items in each category
    names = ["Eric", "Peter", "Arnold", "Alice"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    cigars = ["blue master", "pall mall", "dunhill", "prince"]
    heights = ["tall", "average", "short", "very short"]
    phones = ["google pixel 6", "samsung galaxy s21", "iphone 13", "oneplus 9"]

    # Create Z3 variables for the house position (0..3) of each item
    def make_vars(items):
        d = {}
        for it in items:
            v = Int(it.replace(" ", "_"))
            d[it] = v
        return d

    name_vars = make_vars(names)
    smoothie_vars = make_vars(smoothies)
    cigar_vars = make_vars(cigars)
    height_vars = make_vars(heights)
    phone_vars = make_vars(phones)

    all_vars = []
    for d in [name_vars, smoothie_vars, cigar_vars, height_vars, phone_vars]:
        all_vars.extend(d.values())

    s = Solver()

    # Domain constraints: all in 0..3
    for v in all_vars:
        s.add(v >= 0, v <= 3)

    # All-different constraints within each category
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*smoothie_vars.values()))
    s.add(Distinct(*cigar_vars.values()))
    s.add(Distinct(*height_vars.values()))
    s.add(Distinct(*phone_vars.values()))

    # Helper to access variables by readable names
    Eric = name_vars["Eric"]
    Peter = name_vars["Peter"]
    Arnold = name_vars["Arnold"]
    Alice = name_vars["Alice"]

    dragonfruit = smoothie_vars["dragonfruit"]
    cherry = smoothie_vars["cherry"]
    desert = smoothie_vars["desert"]
    watermelon = smoothie_vars["watermelon"]

    bluemaster = cigar_vars["blue master"]
    pallmall = cigar_vars["pall mall"]
    dunhill = cigar_vars["dunhill"]
    prince = cigar_vars["prince"]

    tall = height_vars["tall"]
    average = height_vars["average"]
    short = height_vars["short"]
    veryshort = height_vars["very short"]

    g_pixel6 = phone_vars["google pixel 6"]
    s_s21 = phone_vars["samsung galaxy s21"]
    iphone13 = phone_vars["iphone 13"]
    oneplus9 = phone_vars["oneplus 9"]

    # Clues encoding
    # 1. The Dragonfruit smoothie lover is Eric.
    s.add(dragonfruit == Eric)
    # 2. The Dunhill smoker is the person who likes Cherry smoothies.
    s.add(dunhill == cherry)
    # 3. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    s.add(s_s21 + 1 == iphone13)
    # 4. The Dunhill smoker is somewhere to the right of the person who is very short.
    s.add(dunhill > veryshort)
    # 5. The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    s.add(watermelon > desert)
    # 6. The Prince smoker is the person who uses a OnePlus 9.
    s.add(prince == oneplus9)
    # 7. The person who is tall is in the third house.
    s.add(tall == 2)  # 0-based index -> house 3
    # 8. The person who is very short is the person who uses an iPhone 13.
    s.add(veryshort == iphone13)
    # 9. The person who smokes Blue Master is not in the first house.
    s.add(bluemaster != 0)
    # 10. The Dunhill smoker is the person who is short.
    s.add(dunhill == short)
    # 11. Peter is not in the third house.
    s.add(Peter != 2)
    # 12. Arnold is the person who uses a Google Pixel 6.
    s.add(Arnold == g_pixel6)
    # 13. The Dragonfruit smoothie lover is the person partial to Pall Mall.
    s.add(dragonfruit == pallmall)

    if s.check() != 1:
        raise RuntimeError("No solution found")

    m = s.model()

    # Invert mapping: house index -> item string
    def invert(dct):
        inv = {}
        for k, v in dct.items():
            inv[m[v].as_long()] = k
        return inv

    pos_to_name = invert(name_vars)
    pos_to_smoothie = invert(smoothie_vars)
    pos_to_cigar = invert(cigar_vars)
    pos_to_height = invert(height_vars)
    pos_to_phone = invert(phone_vars)

    # Build rows for houses 1..4
    rows = []
    for house in range(4):
        rows.append([
            str(house + 1),
            pos_to_name[house],
            pos_to_smoothie[house],
            pos_to_cigar[house],
            pos_to_height[house],
            pos_to_phone[house],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()