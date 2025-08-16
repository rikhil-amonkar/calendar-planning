from z3 import Solver, Int, Distinct, And, Or, sat
import json

# Define attributes
houses = [1, 2, 3]

names = ["Arnold", "Eric", "Peter"]
cigars = ["pall mall", "blue master", "prince"]
animals = ["horse", "cat", "bird"]
children = ["Bella", "Fred", "Meredith"]
books = ["science fiction", "romance", "mystery"]
phones = ["google pixel 6", "iphone 13", "samsung galaxy s21"]

# Create Z3 integer variables for positions of each attribute value
def make_vars(values, prefix):
    return {v: Int(f"{prefix}_{v.replace(' ', '_')}") for v in values}

name_pos = make_vars(names, "Name")
cigar_pos = make_vars(cigars, "Cigar")
animal_pos = make_vars(animals, "Animal")
child_pos = make_vars(children, "Child")
book_pos = make_vars(books, "Book")
phone_pos = make_vars(phones, "Phone")

s = Solver()

# Domain constraints: all positions are within 1..3
for d in [name_pos, cigar_pos, animal_pos, child_pos, book_pos, phone_pos]:
    for v in d.values():
        s.add(And(v >= 1, v <= 3))

# All-different constraints within each category
s.add(Distinct([name_pos[v] for v in names]))
s.add(Distinct([cigar_pos[v] for v in cigars]))
s.add(Distinct([animal_pos[v] for v in animals]))
s.add(Distinct([child_pos[v] for v in children]))
s.add(Distinct([book_pos[v] for v in books]))
s.add(Distinct([phone_pos[v] for v in phones]))

# Clues as constraints

# 1. The person who loves mystery books is the person's child is named Fred.
s.add(book_pos["mystery"] == child_pos["Fred"])

# 2. The cat lover is Eric.
s.add(animal_pos["cat"] == name_pos["Eric"])

# 3. The person partial to Pall Mall is in the second house.
s.add(cigar_pos["pall mall"] == 2)

# 4. The person who keeps horses is the person's child is named Meredith.
s.add(animal_pos["horse"] == child_pos["Meredith"])

# 5. The person's child is named Bella is the Prince smoker.
s.add(child_pos["Bella"] == cigar_pos["prince"])

# 6. The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
s.add(phone_pos["iphone 13"] + 1 == phone_pos["samsung galaxy s21"])

# 7. The person's child is named Fred is directly left of Arnold.
s.add(child_pos["Fred"] + 1 == name_pos["Arnold"])

# 8. Peter is somewhere to the left of Eric.
s.add(name_pos["Peter"] < name_pos["Eric"])

# 9. The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
s.add(book_pos["science fiction"] == phone_pos["samsung galaxy s21"])

# 10. The person who loves science fiction books is in the third house.
s.add(book_pos["science fiction"] == 3)

# 11. The person who loves mystery books is not in the second house.
s.add(book_pos["mystery"] != 2)

assert s.check() == sat
m = s.model()

# Build solution by house
def value_at_house(pos_dict, house):
    for k, v in pos_dict.items():
        if m[v].as_long() == house:
            return k
    return None

rows = []
for h in houses:
    row = [
        str(h),
        value_at_house(name_pos, h),
        value_at_house(cigar_pos, h),
        value_at_house(animal_pos, h),
        value_at_house(child_pos, h),
        value_at_house(book_pos, h),
        value_at_house(phone_pos, h),
    ]
    rows.append(row)

output = {
    "solution": {
        "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
        "rows": rows
    }
}

print(json.dumps(output, ensure_ascii=False, indent=2))