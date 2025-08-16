import json
from z3 import *

# Initialize the solver
s = Solver()

# Define the houses and attributes
houses = [1, 2, 3, 4, 5, 6]
names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
phone_models = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
colors = ["yellow", "red", "green", "blue", "white", "purple"]
sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
phone = {h: String(f"phone_{h}") for h in houses}
cigar = {h: String(f"cigar_{h}") for h in houses}
flower = {h: String(f"flower_{h}") for h in houses}
color = {h: String(f"color_{h}") for h in houses}
sport = {h: String(f"sport_{h}") for h in houses}

# Each attribute must be one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([phone[h] == p for p in phone_models]))
    s.add(Or([cigar[h] == c for c in cigars]))
    s.add(Or([flower[h] == f for f in flowers]))
    s.add(Or([color[h] == c for c in colors]))
    s.add(Or([sport[h] == sp for sp in sports]))

# All attributes in each category must be unique
for attr in [name, phone, cigar, flower, color, sport]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Apply the clues
# Clue 1: The person who uses a OnePlus 9 is in the second house.
s.add(phone[2] == "oneplus 9")

# Clue 2: The person who uses a Xiaomi Mi 11 is somewhere to the left of the person who uses a Huawei P50.
s.add(Exists([h1, h2], And(h1 < h2, phone[h1] == "xiaomi mi 11", phone[h2] == "huawei p50")))

# Clue 3: Carol is the person who loves a carnations arrangement.
s.add(Exists([h], And(name[h] == "Carol", flower[h] == "carnations")))

# Clue 4: The person who loves purple is directly left of the person partial to Pall Mall.
s.add(Exists([h], And(h < 6, color[h] == "purple", cigar[h+1] == "pall mall")))

# Clue 5: The person whose favorite color is green is the person who smokes Blue Master.
s.add(Exists([h], And(color[h] == "green", cigar[h] == "blue master")))

# Clue 6: The person who loves yellow and the person who loves blue are next to each other.
s.add(Or(
    Exists([h], And(h < 6, color[h] == "yellow", color[h+1] == "blue")),
    Exists([h], And(h < 6, color[h] == "blue", color[h+1] == "yellow"))
))

# Clue 7: Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
s.add(Exists([h1, h2], And(h1 < h2, phone[h1] == "samsung galaxy s21", name[h2] == "Eric")))

# Clue 8: There are two houses between Carol and the person who loves a bouquet of daffodils.
s.add(Exists([h1, h2], And(
    name[h1] == "Carol", flower[h2] == "daffodils",
    Or(h2 == h1 + 3, h1 == h2 + 3)
)))

# Clue 9: The Prince smoker is the person who loves basketball.
s.add(Exists([h], And(cigar[h] == "prince", sport[h] == "basketball")))

# Clue 10: The Dunhill smoker is the person who loves volleyball.
s.add(Exists([h], And(cigar[h] == "dunhill", sport[h] == "volleyball")))

# Clue 11: The person who loves swimming is the person who uses a Google Pixel 6.
s.add(Exists([h], And(sport[h] == "swimming", phone[h] == "google pixel 6")))

# Clue 12: The person who uses a Huawei P50 is directly left of the person who loves white.
s.add(Exists([h], And(h < 6, phone[h] == "huawei p50", color[h+1] == "white")))

# Clue 13: The person who uses a OnePlus 9 and the person who loves the rose bouquet are next to each other.
s.add(Or(
    And(phone[1] == "oneplus 9", flower[2] == "roses"),
    And(phone[2] == "oneplus 9", Or(flower[1] == "roses", flower[3] == "roses")),
    And(phone[3] == "oneplus 9", Or(flower[2] == "roses", flower[4] == "roses")),
    And(phone[4] == "oneplus 9", Or(flower[3] == "roses", flower[5] == "roses")),
    And(phone[5] == "oneplus 9", Or(flower[4] == "roses", flower[6] == "roses")),
    And(phone[6] == "oneplus 9", flower[5] == "roses")
))

# Clue 14: The person who loves the bouquet of iris is somewhere to the left of Eric.
s.add(Exists([h1, h2], And(h1 < h2, flower[h1] == "iris", name[h2] == "Eric")))

# Clue 15: The Dunhill smoker is Peter.
s.add(Exists([h], And(cigar[h] == "dunhill", name[h] == "Peter")))

# Clue 16: The person who loves blue is Peter.
s.add(Exists([h], And(color[h] == "blue", name[h] == "Peter")))

# Clue 17: The person who loves the vase of tulips is Bob.
s.add(Exists([h], And(flower[h] == "tulips", name[h] == "Bob")))

# Clue 18: Alice is in the first house.
s.add(name[1] == "Alice")

# Clue 19: The person who loves baseball is directly left of the person who smokes Blue Master.
s.add(Exists([h], And(h < 6, sport[h] == "baseball", cigar[h+1] == "blue master")))

# Clue 20: The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes many unique blends.
s.add(Exists([h1, h2], And(h1 < h2, cigar[h1] == "blends", phone[h2] == "google pixel 6")))

# Clue 21: The person who loves soccer is Carol.
s.add(Exists([h], And(name[h] == "Carol", sport[h] == "soccer")))

# Clue 22: The person who loves a carnations arrangement is directly left of the person who smokes many unique blends.
s.add(Exists([h], And(h < 6, flower[h] == "carnations", cigar[h+1] == "blends")))

# Clue 23: Eric is the person who smokes many unique blends.
s.add(Exists([h], And(name[h] == "Eric", cigar[h] == "blends")))

# Clue 24: The person who loves volleyball is the person who uses an iPhone 13.
s.add(Exists([h], And(sport[h] == "volleyball", phone[h] == "iphone 13")))

# Solve the problem
if s.check() == sat:
    m = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
            "rows": []
        }
    }
    for h in sorted(houses):
        row = [
            str(h),
            m.eval(name[h]).as_string(),
            m.eval(phone[h]).as_string(),
            m.eval(cigar[h]).as_string(),
            m.eval(flower[h]).as_string(),
            m.eval(color[h]).as_string(),
            m.eval(sport[h]).as_string()
        ]
        # Replace quotes for proper JSON formatting
        row = [x.replace('"', '') for x in row]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")