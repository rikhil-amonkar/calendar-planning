from z3 import *
import json

# Create a Z3 solver
s = Solver()

# Every house number is an integer between 1 and 6. 
houses = [Int(f"house_{i}") for i in range(1,7)]  # not used directly, but domain is [1,6]

# Helper: every variable representing a placement must be in 1..6.
def in_range(x):
    return And(x >= 1, x <= 6)

# ------------------------
# Define variables for each category.
# For names:
names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
pName = { n: Int(f"name_{n.replace(' ', '_')}") for n in names }
for v in pName.values():
    s.add(in_range(v))
s.add(Distinct(list(pName.values())))
# Given: Alice is in the first house.
s.add(pName["Alice"] == 1)

# For phone models:
phones = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
pPhone = { ph: Int(f"phone_{ph.replace(' ', '_')}") for ph in phones }
for v in pPhone.values():
    s.add(in_range(v))
s.add(Distinct(list(pPhone.values())))
# Clue 1: oneplus 9 is in the second house.
s.add(pPhone["oneplus 9"] == 2)
# Clue 2: xiaomi mi 11 is somewhere to the left of huawei p50.
s.add(pPhone["xiaomi mi 11"] < pPhone["huawei p50"])
# Clue 11: The person who loves swimming is the person who uses a Google Pixel 6.
# (We add that later in sports)
# Clue 12: The person who uses a Huawei P50 is directly left of the person who loves white 
#   => phone_huawei_p50 + 1 == color_white (will add when color is defined)
# Clue 20: The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes blends.
#   We express that as: phone_google_pixel_6 > (house number of the person with blends) (see cigars)

# For cigars:
cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
pCigar = { c: Int(f"cigar_{c.replace(' ', '_')}") for c in cigars }
for v in pCigar.values():
    s.add(in_range(v))
s.add(Distinct(list(pCigar.values())))
# Clue 15: The Dunhill smoker is Peter.
s.add(pCigar["dunhill"] == pName["Peter"])
# Clue 23: Eric is the person who smokes many unique blends.
s.add(pCigar["blends"] == pName["Eric"])
# Clue 22: The person who loves a carnations arrangement is directly left of the person who smokes blends.
#   => flower_carnations + 1 == cigar_blends (will add when flowers are defined)
# Clue 9: The Prince smoker is the person who loves basketball.
#   => cigar_prince == sport_basketball (see sports)
# Clue 19: The person who loves baseball is directly left of the person who smokes Blue Master.
#   => sport_baseball + 1 == cigar_blue_master (see sports)
# Clue 4: The person who loves purple is directly left of the person partial to Pall Mall.
#   => color_purple + 1 == cigar_pall mall

# For flowers:
flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
pFlower = { f: Int(f"flower_{f.replace(' ', '_')}") for f in flowers }
for v in pFlower.values():
    s.add(in_range(v))
s.add(Distinct(list(pFlower.values())))
# Clue 3: Carol is the person who loves a carnations arrangement.
s.add(pFlower["carnations"] == pName["Carol"])
# Clue 13: The person who uses a OnePlus 9 and the person who loves the rose bouquet are next to each other.
s.add(Abs(pPhone["oneplus 9"] - pFlower["roses"]) == 1)
# Clue 14: The person who loves the bouquet of iris is somewhere to the left of Eric.
s.add(pFlower["iris"] < pName["Eric"])
# Clue 17: The person who loves the vase of tulips is Bob.
s.add(pFlower["tulips"] == pName["Bob"])
# Clue 8: There are two houses between Carol and the person who loves a bouquet of daffodils.
s.add(Abs(pName["Carol"] - pFlower["daffodils"]) == 3)

# For colors:
colors = ["yellow", "red", "green", "blue", "white", "purple"]
pColor = { col: Int(f"color_{col}") for col in colors }
for v in pColor.values():
    s.add(in_range(v))
s.add(Distinct(list(pColor.values())))
# Clue 16: The person who loves blue is Peter.
s.add(pColor["blue"] == pName["Peter"])
# Clue 6: The person who loves yellow and the person who loves blue are next to each other.
s.add(Or(And(pColor["yellow"] - pColor["blue"] == 1), And(pColor["blue"] - pColor["yellow"] == 1)))
# Clue 5: The person whose favorite color is green is the person who smokes Blue Master.
s.add(pColor["green"] == pCigar["blue master"])
# Clue 4: The person who loves purple is directly left of the person partial to Pall Mall.
s.add(pColor["purple"] + 1 == pCigar["pall mall"])
# Clue 12 (continued): Huawei p50 is directly left of the person who loves white.
s.add(pPhone["huawei p50"] + 1 == pColor["white"])

# For favorite sports:
sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]
pSport = { sp: Int(f"sport_{sp}") for sp in sports }
for v in pSport.values():
    s.add(in_range(v))
s.add(Distinct(list(pSport.values())))
# Clue 21: The person who loves soccer is Carol.
s.add(pSport["soccer"] == pName["Carol"])
# Clue 10: The Dunhill smoker is the person who loves volleyball.
s.add(pSport["volleyball"] == pName["Peter"])
# Clue 24: The person who loves volleyball is the person who uses an iPhone 13.
s.add(pSport["volleyball"] == pPhone["iphone 13"])
# Clue 11: The person who loves swimming is the person who uses a Google Pixel 6.
s.add(pSport["swimming"] == pPhone["google pixel 6"])
# Clue 9: The Prince smoker is the person who loves basketball.
s.add(pCigar["prince"] == pSport["basketball"])
# Clue 19: The person who loves baseball is directly left of the person who smokes Blue Master.
s.add(pSport["baseball"] + 1 == pCigar["blue master"])
# Clue 20: The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes many unique blends.
# (Eric smokes blends) thus:
s.add(pPhone["google pixel 6"] > pName["Eric"])
    
# Clue 22: The person who loves a carnations arrangement is directly left of the person who smokes many unique blends.
s.add(pFlower["carnations"] + 1 == pCigar["blends"])

# Clue 7: Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
s.add(pName["Eric"] > pPhone["samsung galaxy s21"])

# Additionally, from Clue 20 we already used Eric for blends.

# Also, from Clue 15 & 10 we know:
#   Peter's cigar is dunhill and his sport (volleyball) is with iPhone 13 (already added).

# Finally, enforce the relationship from Clue 20 (already added above) and
# Clue 2 (already added above).

# Now, let's add any additional ordering we deduced in our solution.

# Our solution (which we expect) is:
#   House 1: Alice, samsung galaxy s21, yellow monster, iris, red, baseball.
#   House 2: Carol, oneplus 9, blue master, carnations, green, soccer.
#   House 3: Eric, xiaomi mi 11, blends, roses, yellow, tennis.
#   House 4: Peter, iphone 13, dunhill, lilies, blue, volleyball.
#   House 5: Arnold, huawei p50, prince, daffodils, purple, basketball.
#   House 6: Bob, google pixel 6, pall mall, tulips, white, swimming.
#
# To help the solver converge to a solution that matches our intended one (if many exist)
# we add these as soft hints (not required, but they are consistent with all constraints):

s.add(pName["Alice"] == 1)
s.add(pPhone["oneplus 9"] == 2)
# We'll not add extra "hint" constraints; the above constraints force a unique solution.

# Check for a solution:
if s.check() == sat:
    m = s.model()
    # We want to form dictionaries that map house number -> attribute string for each category.
    
    # Helper: For a category dictionary, invert by house number.
    def invert_category(cat):
        mapping = {}
        for key, var in cat.items():
            # m[var] is a Z3 numeral. Convert to int.
            house_num = m[var].as_long()
            mapping[house_num] = key
        return mapping

    name_by_house = invert_category(pName)
    phone_by_house = invert_category(pPhone)
    cigar_by_house = invert_category(pCigar)
    flower_by_house = invert_category(pFlower)
    color_by_house = invert_category(pColor)
    sport_by_house = invert_category(pSport)
    
    # Build the rows sorted by house number from 1 to 6.
    rows = []
    header = ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"]
    for house in range(1, 7):
        row = [
            str(house),
            name_by_house.get(house, "?"),
            phone_by_house.get(house, "?"),
            cigar_by_house.get(house, "?"),
            flower_by_house.get(house, "?"),
            color_by_house.get(house, "?"),
            sport_by_house.get(house, "?")
        ]
        rows.append(row)
    
    # The final JSON output has the required structure.
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found")