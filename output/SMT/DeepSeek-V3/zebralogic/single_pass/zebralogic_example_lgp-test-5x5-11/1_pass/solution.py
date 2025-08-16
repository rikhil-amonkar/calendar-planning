import json
from z3 import *

# Initialize the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define attributes
names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
heights = ['average', 'very tall', 'very short', 'short', 'tall']
cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

# Create variables for each attribute in each house
name = {h: String(f'name_{h}') for h in houses}
height = {h: String(f'height_{h}') for h in houses}
cigar = {h: String(f'cigar_{h}') for h in houses}
smoothie = {h: String(f'smoothie_{h}') for h in houses}
phone = {h: String(f'phone_{h}') for h in houses}

# Each attribute in each house must be one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([height[h] == ht for ht in heights]))
    s.add(Or([cigar[h] == c for c in cigars]))
    s.add(Or([smoothie[h] == sm for sm in smoothies]))
    s.add(Or([phone[h] == p for p in phones]))

# All attributes in each category must be distinct
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([height[h] for h in houses]))
s.add(Distinct([cigar[h] for h in houses]))
s.add(Distinct([smoothie[h] for h in houses]))
s.add(Distinct([phone[h] for h in houses]))

# Add constraints based on the clues
# Clue 15: The person who uses an iPhone 13 is Eric.
for h in houses:
    s.add(Implies(phone[h] == 'iphone 13', name[h] == 'Eric'))

# Clue 6: Eric is very tall.
for h in houses:
    s.add(Implies(name[h] == 'Eric', height[h] == 'very tall'))

# Clue 10: Bob is the Dunhill smoker.
for h in houses:
    s.add(Implies(name[h] == 'Bob', cigar[h] == 'dunhill'))

# Clue 5: The person who is average height is the Dunhill smoker.
for h in houses:
    s.add(Implies(height[h] == 'average', cigar[h] == 'dunhill'))

# Since Bob is the Dunhill smoker (clue 10), and average height is Dunhill smoker (clue 5), Bob is average height.
for h in houses:
    s.add(Implies(name[h] == 'Bob', height[h] == 'average'))

# Clue 11: The Dragonfruit smoothie lover is Bob.
for h in houses:
    s.add(Implies(name[h] == 'Bob', smoothie[h] == 'dragonfruit'))

# Clue 14: There are two houses between the person who is very tall (Eric) and the Dragonfruit smoothie lover (Bob).
# So if Eric is in h, Bob is in h+3, or Eric is in h, Bob is in h-3. But houses are 1-5.
for h in houses:
    for h2 in houses:
        if h + 3 == h2:
            s.add(Implies(And(name[h] == 'Eric', height[h] == 'very tall'), name[h2] == 'Bob'))
        if h - 3 == h2:
            s.add(Implies(And(name[h] == 'Eric', height[h] == 'very tall'), name[h2] == 'Bob'))

# Clue 2: There is one house between Eric and Alice.
# So Alice is either two to the right or two to the left of Eric.
for h in houses:
    for h2 in houses:
        if h + 2 == h2:
            s.add(Implies(name[h] == 'Eric', name[h2] == 'Alice'))
        if h - 2 == h2:
            s.add(Implies(name[h] == 'Eric', name[h2] == 'Alice'))

# Clue 9: Eric is directly left of the person who likes Cherry smoothies.
# So Eric is in h, cherry lover is in h+1.
for h in houses:
    if h + 1 in houses:
        s.add(Implies(name[h] == 'Eric', smoothie[h+1] == 'cherry'))

# Clue 4: The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
# So iPhone 13 user is in h, blue master smoker is in h+1.
for h in houses:
    if h + 1 in houses:
        s.add(Implies(phone[h] == 'iphone 13', cigar[h+1] == 'blue master'))

# Clue 12: The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
# So they are in h and h+1 or h and h-1.
for h in houses:
    if h + 1 in houses:
        s.add(Or(
            And(phone[h] == 'iphone 13', phone[h+1] == 'oneplus 9'),
            And(phone[h] == 'oneplus 9', phone[h+1] == 'iphone 13')
        ))
    if h - 1 in houses:
        s.add(Or(
            And(phone[h] == 'iphone 13', phone[h-1] == 'oneplus 9'),
            And(phone[h] == 'oneplus 9', phone[h-1] == 'iphone 13')
        ))

# Clue 7: Arnold is directly left of the person who uses a Huawei P50.
# So Arnold is in h, Huawei P50 user is in h+1.
for h in houses:
    if h + 1 in houses:
        s.add(Implies(name[h] == 'Arnold', phone[h+1] == 'huawei p50'))

# Clue 8: Bob is not in the fourth house.
s.add(Not(name[4] == 'Bob'))

# Clue 3: The person who is short is the person who smokes blends.
for h in houses:
    s.add(Implies(height[h] == 'short', cigar[h] == 'blends'))

# Clue 13: The person who uses a Samsung Galaxy S21 is the person who is short.
for h in houses:
    s.add(Implies(phone[h] == 'samsung galaxy s21', height[h] == 'short'))

# Clue 1: The Prince smoker is the Desert smoothie lover.
for h in houses:
    s.add(Implies(cigar[h] == 'prince', smoothie[h] == 'desert'))

# Clue 16: The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
# So for any house h with desert, there exists a house h2 > h with lime.
s.add(Or(
    And(smoothie[1] == 'desert', Or([smoothie[h] == 'lime' for h in [2,3,4,5]])),
    And(smoothie[2] == 'desert', Or([smoothie[h] == 'lime' for h in [3,4,5]])),
    And(smoothie[3] == 'desert', Or([smoothie[h] == 'lime' for h in [4,5]])),
    And(smoothie[4] == 'desert', smoothie[5] == 'lime'))
)

# Clue 17: Arnold and the person who is very short are next to each other.
# So Arnold is in h, very short is in h+1 or h-1.
for h in houses:
    if h + 1 in houses:
        s.add(Or(
            And(name[h] == 'Arnold', height[h+1] == 'very short'),
            And(name[h+1] == 'Arnold', height[h] == 'very short')
        ))
    if h - 1 in houses:
        s.add(Or(
            And(name[h] == 'Arnold', height[h-1] == 'very short'),
            And(name[h-1] == 'Arnold', height[h] == 'very short')
        ))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            str(model.eval(name[h])),
            str(model.eval(height[h])),
            str(model.eval(cigar[h])),
            str(model.eval(smoothie[h])),
            str(model.eval(phone[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")