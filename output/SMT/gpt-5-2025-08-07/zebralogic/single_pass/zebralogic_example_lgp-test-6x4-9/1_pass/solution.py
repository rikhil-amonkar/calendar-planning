from z3 import Solver, Int, Distinct, And, Or
import json

# Domains
NAMES = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
PHONES = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
NATS = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
COLORS = ["blue", "red", "yellow", "green", "white", "purple"]

name_idx = {v: i for i, v in enumerate(NAMES)}
phone_idx = {v: i for i, v in enumerate(PHONES)}
nat_idx = {v: i for i, v in enumerate(NATS)}
color_idx = {v: i for i, v in enumerate(COLORS)}

# Variables per house (0-based houses 0..5 correspond to 1..6)
name = [Int(f"name_{i}") for i in range(6)]
phone = [Int(f"phone_{i}") for i in range(6)]
nat = [Int(f"nat_{i}") for i in range(6)]
color = [Int(f"color_{i}") for i in range(6)]

s = Solver()

# Domain constraints
for i in range(6):
    s.add(And(name[i] >= 0, name[i] < 6))
    s.add(And(phone[i] >= 0, phone[i] < 6))
    s.add(And(nat[i] >= 0, nat[i] < 6))
    s.add(And(color[i] >= 0, color[i] < 6))

# All-different per attribute
s.add(Distinct(name))
s.add(Distinct(phone))
s.add(Distinct(nat))
s.add(Distinct(color))

# Helper to assert "A iff B" at same house across all i
def eq_across(attribute_a, idx_a, attribute_b, idx_b):
    for i in range(6):
        s.add( (attribute_a[i] == idx_a) == (attribute_b[i] == idx_b) )

# Clues encoding:

# 1. Carol is not in the third house.
s.add(name[2] != name_idx["Carol"])

# 2. There is one house between the Dane and the British person.
for i in range(6):
    s.add(
        Or(
            nat[i] != nat_idx["dane"],
            Or(
                (i + 2 < 6) & (nat[i + 2] == nat_idx["brit"]),
                (i - 2 >= 0) & (nat[i - 2] == nat_idx["brit"])
            )
        )
    )

# 3. Carol is the person whose favorite color is green.
eq_across(name, name_idx["Carol"], color, color_idx["green"])

# 4. Arnold is directly left of Alice.
s.add(Or(*[And(name[i] == name_idx["Arnold"], name[i + 1] == name_idx["Alice"]) for i in range(5)]))

# 5. Alice is the German.
eq_across(name, name_idx["Alice"], nat, nat_idx["german"])

# 6. OnePlus 9 user loves purple.
eq_across(phone, phone_idx["oneplus 9"], color, color_idx["purple"])

# 7. Huawei P50 is not in the third house.
s.add(phone[2] != phone_idx["huawei p50"])

# 8. Samsung Galaxy S21 is in the fifth house.
s.add(phone[4] == phone_idx["samsung galaxy s21"])

# 9. White is somewhere to the right of red.
s.add(Or(*[And(color[i] == color_idx["red"], color[j] == color_idx["white"]) for i in range(6) for j in range(i+1, 6)]))

# 10. The person who uses a Samsung Galaxy S21 is Bob.
eq_across(phone, phone_idx["samsung galaxy s21"], name, name_idx["Bob"])

# 11. The Dane loves yellow.
eq_across(nat, nat_idx["dane"], color, color_idx["yellow"])

# 12. The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
s.add(Or(*[And(phone[i] == phone_idx["samsung galaxy s21"], name[j] == name_idx["Peter"]) for i in range(6) for j in range(i+1, 6)]))

# 13. The person who loves blue is Peter.
eq_across(color, color_idx["blue"], name, name_idx["Peter"])

# 14. Peter is the British person.
eq_across(name, name_idx["Peter"], nat, nat_idx["brit"])

# 15. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
s.add(Or(*[And(phone[i] == phone_idx["samsung galaxy s21"], phone[i + 1] == phone_idx["iphone 13"]) for i in range(5)]))

# 16. The Norwegian is the person who loves purple.
eq_across(nat, nat_idx["norwegian"], color, color_idx["purple"])

# 17. The person who uses a Xiaomi Mi 11 is the Chinese.
eq_across(phone, phone_idx["xiaomi mi 11"], nat, nat_idx["chinese"])

# Solve
if s.check() != 1:  # 1 == sat
    raise RuntimeError("Puzzle is unsatisfiable")

m = s.model()

# Build JSON output
header = ["House", "Name", "PhoneModel", "Nationality", "Color"]

rows = []
for i in range(6):
    row = [
        str(i + 1),
        NAMES[m.evaluate(name[i]).as_long()],
        PHONES[m.evaluate(phone[i]).as_long()],
        NATS[m.evaluate(nat[i]).as_long()],
        COLORS[m.evaluate(color[i]).as_long()],
    ]
    rows.append(row)

solution = {
    "solution": {
        "header": header,
        "rows": rows
    }
}

print(json.dumps(solution, ensure_ascii=False))