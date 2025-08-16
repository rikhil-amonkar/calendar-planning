import json
from z3 import Int, Solver, Distinct, Or, And, sat

# Houses are indexed 0..5 (representing houses 1..6)
houses = list(range(6))

# Domains
names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
phones = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

# Position variables (house index for each attribute value)
pos_name = {n: Int(f"name_{n}_pos") for n in names}
pos_height = {h: Int(f"height_{h.replace(' ', '_')}_pos") for h in heights}
pos_phone = {p: Int(f"phone_{p.replace(' ', '_')}_pos") for p in phones}

s = Solver()

# Each position variable domain: 0..5
for v in list(pos_name.values()) + list(pos_height.values()) + list(pos_phone.values()):
    s.add(v >= 0, v <= 5)

# AllDifferent within each category (each house has exactly one name/height/phone)
s.add(Distinct([pos_name[n] for n in names]))
s.add(Distinct([pos_height[h] for h in heights]))
s.add(Distinct([pos_phone[p] for p in phones]))

# Clues:
# 1. Bob is directly left of the person who is tall.
s.add(pos_name["Bob"] + 1 == pos_height["tall"])

# 2. Peter is somewhere to the left of the person who uses an iPhone 13.
s.add(pos_name["Peter"] < pos_phone["iphone 13"])

# 3. The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
s.add(pos_height["very short"] > pos_phone["google pixel 6"])

# 4. Carol is the person who is very tall.
s.add(pos_name["Carol"] == pos_height["very tall"])

# 5. There is one house between the person who uses a Google Pixel 6 and the person who is short.
s.add(Or(pos_phone["google pixel 6"] == pos_height["short"] + 2,
         pos_phone["google pixel 6"] == pos_height["short"] - 2))

# 6. The person who uses a Samsung Galaxy S21 is not in the first house.
s.add(pos_phone["samsung galaxy s21"] != 0)

# 7. The person who uses a OnePlus 9 is directly left of the person who is short.
s.add(pos_phone["oneplus 9"] + 1 == pos_height["short"])

# 8. The person who is tall is Arnold.
s.add(pos_height["tall"] == pos_name["Arnold"])

# 9. The person who is super tall is in the first house.
s.add(pos_height["super tall"] == 0)

# 10. The person who uses a Xiaomi Mi 11 is Carol.
s.add(pos_phone["xiaomi mi 11"] == pos_name["Carol"])

# 11. The person who uses a Google Pixel 6 is somewhere to the right of Eric.
s.add(pos_phone["google pixel 6"] > pos_name["Eric"])

# 12. The person who is short is in the sixth house.
s.add(pos_height["short"] == 5)

# Solve
if s.check() != sat:
    raise RuntimeError("No solution found")

m = s.model()

# Build reverse lookup for each house
house_to_name = {}
house_to_height = {}
house_to_phone = {}

for n in names:
    house_to_name[m[pos_name[n]].as_long()] = n
for h in heights:
    house_to_height[m[pos_height[h]].as_long()] = h
for p in phones:
    house_to_phone[m[pos_phone[p]].as_long()] = p

# Prepare JSON output
rows = []
for i in range(6):
    house_num_str = str(i + 1)
    rows.append([
        house_num_str,
        house_to_name[i],
        house_to_height[i],
        house_to_phone[i]
    ])

output = {
    "solution": {
        "header": ["House", "Name", "Height", "PhoneModel"],
        "rows": rows
    }
}

print(json.dumps(output, ensure_ascii=False))