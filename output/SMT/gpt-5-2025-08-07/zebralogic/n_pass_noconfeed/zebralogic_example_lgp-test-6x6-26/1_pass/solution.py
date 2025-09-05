import json
from z3 import *

def sanitize(s):
    return s.lower().replace(" ", "_").replace("-", "_")

# Categories and values
houses = list(range(1, 7))

names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
phones = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
colors = ["yellow", "red", "green", "blue", "white", "purple"]
sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

# Create Z3 variables for each value representing its house position (1..6)
def create_vars(values, prefix):
    return {v: Int(f"{prefix}_{sanitize(v)}") for v in values}

name_pos = create_vars(names, "name")
phone_pos = create_vars(phones, "phone")
cigar_pos = create_vars(cigars, "cigar")
flower_pos = create_vars(flowers, "flower")
color_pos = create_vars(colors, "color")
sport_pos = create_vars(sports, "sport")

all_vars = []
for group in [name_pos, phone_pos, cigar_pos, flower_pos, color_pos, sport_pos]:
    all_vars.extend(list(group.values()))

s = Solver()

# Domain constraints (1..6)
for v in all_vars:
    s.add(And(v >= 1, v <= 6))

# AllDifferent constraints within each category
s.add(Distinct(*name_pos.values()))
s.add(Distinct(*phone_pos.values()))
s.add(Distinct(*cigar_pos.values()))
s.add(Distinct(*flower_pos.values()))
s.add(Distinct(*color_pos.values()))
s.add(Distinct(*sport_pos.values()))

# Helper for adjacency (next to)
def next_to(a, b):
    return Or(a - b == 1, b - a == 1)

# Clues:

# 1. The person who uses a OnePlus 9 is in the second house.
s.add(phone_pos["oneplus 9"] == 2)

# 2. Xiaomi Mi 11 is somewhere to the left of Huawei P50.
s.add(phone_pos["xiaomi mi 11"] < phone_pos["huawei p50"])

# 3. Carol loves carnations.
s.add(name_pos["Carol"] == flower_pos["carnations"])

# 4. Purple is directly left of Pall Mall.
s.add(color_pos["purple"] + 1 == cigar_pos["pall mall"])

# 5. Green is Blue Master.
s.add(color_pos["green"] == cigar_pos["blue master"])

# 6. Yellow and Blue are next to each other.
s.add(next_to(color_pos["yellow"], color_pos["blue"]))

# 7. Eric is right of Samsung Galaxy S21.
s.add(name_pos["Eric"] > phone_pos["samsung galaxy s21"])

# 8. Two houses between Carol and Daffodils.
s.add(Abs(name_pos["Carol"] - flower_pos["daffodils"]) == 3)

# 9. Prince smoker loves basketball.
s.add(cigar_pos["prince"] == sport_pos["basketball"])

# 10. Dunhill smoker loves volleyball.
s.add(cigar_pos["dunhill"] == sport_pos["volleyball"])

# 11. Swimming uses Google Pixel 6.
s.add(sport_pos["swimming"] == phone_pos["google pixel 6"])

# 12. Huawei P50 is directly left of White.
s.add(phone_pos["huawei p50"] + 1 == color_pos["white"])

# 13. OnePlus 9 and Roses are next to each other.
s.add(next_to(phone_pos["oneplus 9"], flower_pos["roses"]))

# 14. Iris is left of Eric.
s.add(flower_pos["iris"] < name_pos["Eric"])

# 15. Dunhill smoker is Peter.
s.add(cigar_pos["dunhill"] == name_pos["Peter"])

# 16. Blue is Peter.
s.add(color_pos["blue"] == name_pos["Peter"])

# 17. Tulips is Bob.
s.add(flower_pos["tulips"] == name_pos["Bob"])

# 18. Alice is in the first house.
s.add(name_pos["Alice"] == 1)

# 19. Baseball is directly left of Blue Master.
s.add(sport_pos["baseball"] + 1 == cigar_pos["blue master"])

# 20. Google Pixel 6 is right of Blends.
s.add(phone_pos["google pixel 6"] > cigar_pos["blends"])

# 21. Soccer is Carol.
s.add(sport_pos["soccer"] == name_pos["Carol"])

# 22. Carnations is directly left of Blends.
s.add(flower_pos["carnations"] + 1 == cigar_pos["blends"])

# 23. Eric is Blends.
s.add(name_pos["Eric"] == cigar_pos["blends"])

# 24. Volleyball is iPhone 13.
s.add(sport_pos["volleyball"] == phone_pos["iphone 13"])

# Solve
if s.check() != sat:
    # Fallback: output empty structure if unsat (should not happen)
    output = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
            "rows": [[str(i), "", "", "", "", "", ""] for i in houses]
        }
    }
    print(json.dumps(output, ensure_ascii=False))
else:
    m = s.model()

    # Invert mappings: house -> value
    def invert(pos_map):
        inv = {}
        for k, v in pos_map.items():
            inv[m.evaluate(v).as_long()] = k
        return inv

    inv_name = invert(name_pos)
    inv_phone = invert(phone_pos)
    inv_cigar = invert(cigar_pos)
    inv_flower = invert(flower_pos)
    inv_color = invert(color_pos)
    inv_sport = invert(sport_pos)

    rows = []
    for h in houses:
        row = [
            str(h),
            inv_name[h],
            inv_phone[h],
            inv_cigar[h],
            inv_flower[h],
            inv_color[h],
            inv_sport[h]
        ]
        rows.append(row)

    output = {
      "solution": {
        "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
        "rows": rows
      }
    }
    print(json.dumps(output, ensure_ascii=False))