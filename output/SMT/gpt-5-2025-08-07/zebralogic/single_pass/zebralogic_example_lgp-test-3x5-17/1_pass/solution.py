import json
import re
from z3 import Int, Solver, Distinct, And, sat

def safe(sym):
    return re.sub(r'[^a-zA-Z0-9_]', '_', sym.lower())

# Domains
houses = [1, 2, 3]

names = ["Eric", "Arnold", "Peter"]
phones = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
heights = ["very short", "average", "short"]
styles = ["colonial", "ranch", "victorian"]
cars = ["tesla model 3", "toyota camry", "ford f150"]

# Z3 variables: position (house index) of each attribute value
pos_name = {n: Int(f"name_{safe(n)}") for n in names}
pos_phone = {p: Int(f"phone_{safe(p)}") for p in phones}
pos_height = {h: Int(f"height_{safe(h)}") for h in heights}
pos_style = {s: Int(f"style_{safe(s)}") for s in styles}
pos_car = {c: Int(f"car_{safe(c)}") for c in cars}

s = Solver()

# Helper: constrain all variables to be in houses and distinct per category
def in_domain_and_distinct(dct):
    vars_ = list(dct.values())
    for v in vars_:
        s.add(And(v >= 1, v <= 3))
    s.add(Distinct(vars_))

in_domain_and_distinct(pos_name)
in_domain_and_distinct(pos_phone)
in_domain_and_distinct(pos_height)
in_domain_and_distinct(pos_style)
in_domain_and_distinct(pos_car)

# Clues as constraints
# 1. Peter is somewhere to the right of Eric.
s.add(pos_name["Peter"] > pos_name["Eric"])

# 2. The person living in a colonial-style house is in the second house.
s.add(pos_style["colonial"] == 2)

# 3. The person who owns a Tesla Model 3 is the person who is very short.
s.add(pos_car["tesla model 3"] == pos_height["very short"])

# 4. The person who is short is directly left of the person who uses a Samsung Galaxy S21.
s.add(pos_height["short"] + 1 == pos_phone["samsung galaxy s21"])

# 5. The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
s.add(pos_phone["iphone 13"] + 1 == pos_phone["google pixel 6"])

# 6. The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
s.add(pos_style["colonial"] > pos_style["ranch"])

# 7. Arnold is in the second house.
s.add(pos_name["Arnold"] == 2)

# 8. The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
s.add(pos_car["ford f150"] > pos_car["toyota camry"])

# 9. The person who has an average height is in the first house.
s.add(pos_height["average"] == 1)

assert s.check() == sat
m = s.model()

# Build inverse mappings: house -> attribute value
def invert(pos_map):
    inv = {}
    for k, v in pos_map.items():
        inv[m[v].as_long()] = k
    return inv

name_by_house = invert(pos_name)
phone_by_house = invert(pos_phone)
height_by_house = invert(pos_height)
style_by_house = invert(pos_style)
car_by_house = invert(pos_car)

solution = {
    "solution": {
        "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
        "rows": []
    }
}

for h in houses:
    solution["solution"]["rows"].append([
        str(h),
        name_by_house[h],
        phone_by_house[h],
        height_by_house[h],
        style_by_house[h],
        car_by_house[h],
    ])

print(json.dumps(solution))