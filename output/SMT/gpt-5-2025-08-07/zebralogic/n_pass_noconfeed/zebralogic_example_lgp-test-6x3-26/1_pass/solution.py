import json
from z3 import Solver, Int, Distinct, And, Or, Abs

def sanitize(s):
    return s.lower().replace(' ', '_')

# Attributes
names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
phones = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

# Index maps
Name = {n: i for i, n in enumerate(names)}
Height = {h: i for i, h in enumerate(heights)}
Phone = {p: i for i, p in enumerate(phones)}

# Variables: position (0..5) of each attribute value
name_pos = [Int(f"name_pos_{sanitize(n)}") for n in names]
height_pos = [Int(f"height_pos_{sanitize(h)}") for h in heights]
phone_pos = [Int(f"phone_pos_{sanitize(p)}") for p in phones]

s = Solver()

# Domain and uniqueness constraints
for arr in [name_pos, height_pos, phone_pos]:
    for v in arr:
        s.add(And(v >= 0, v <= 5))
    s.add(Distinct(*arr))

# Clues:
# 1. Bob is directly left of the person who is tall.
s.add(name_pos[Name["Bob"]] + 1 == height_pos[Height["tall"]])

# 2. Peter is somewhere to the left of the person who uses an iPhone 13.
s.add(name_pos[Name["Peter"]] < phone_pos[Phone["iphone 13"]])

# 3. The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
s.add(height_pos[Height["very short"]] > phone_pos[Phone["google pixel 6"]])

# 4. Carol is the person who is very tall.
s.add(name_pos[Name["Carol"]] == height_pos[Height["very tall"]])

# 5. There is one house between the person who uses a Google Pixel 6 and the person who is short.
s.add(Abs(phone_pos[Phone["google pixel 6"]] - height_pos[Height["short"]]) == 2)

# 6. The person who uses a Samsung Galaxy S21 is not in the first house.
s.add(phone_pos[Phone["samsung galaxy s21"]] != 0)

# 7. The person who uses a OnePlus 9 is directly left of the person who is short.
s.add(phone_pos[Phone["oneplus 9"]] + 1 == height_pos[Height["short"]])

# 8. The person who is tall is Arnold.
s.add(height_pos[Height["tall"]] == name_pos[Name["Arnold"]])

# 9. The person who is super tall is in the first house.
s.add(height_pos[Height["super tall"]] == 0)

# 10. The person who uses a Xiaomi Mi 11 is Carol.
s.add(phone_pos[Phone["xiaomi mi 11"]] == name_pos[Name["Carol"]])

# 11. The person who uses a Google Pixel 6 is somewhere to the right of Eric.
s.add(phone_pos[Phone["google pixel 6"]] > name_pos[Name["Eric"]])

# 12. The person who is short is in the sixth house.
s.add(height_pos[Height["short"]] == 5)

assert s.check().r == 1  # sat

m = s.model()

# Build house-wise mappings
house_to_name = {}
house_to_height = {}
house_to_phone = {}

for i, n in enumerate(names):
    house_to_name[m[name_pos[i]].as_long()] = n

for i, h in enumerate(heights):
    house_to_height[m[height_pos[i]].as_long()] = h

for i, p in enumerate(phones):
    house_to_phone[m[phone_pos[i]].as_long()] = p

rows = []
for h in range(6):
    rows.append([str(h + 1), house_to_name[h], house_to_height[h], house_to_phone[h]])

output = {
    "solution": {
        "header": ["House", "Name", "Height", "PhoneModel"],
        "rows": rows
    }
}

print(json.dumps(output, ensure_ascii=False))