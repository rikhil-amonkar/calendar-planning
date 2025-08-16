from z3 import *

# Create a solver instance
s = Solver()

num_houses = 5

# We use 0-indexed houses.
# Define variables for each attribute per house.
# Domain for each variable is 0..4.
names    = [Int(f"name_{i}") for i in range(num_houses)]
food     = [Int(f"food_{i}") for i in range(num_houses)]
car      = [Int(f"car_{i}") for i in range(num_houses)]
phone    = [Int(f"phone_{i}") for i in range(num_houses)]
occ      = [Int(f"occ_{i}") for i in range(num_houses)]
drink    = [Int(f"drink_{i}") for i in range(num_houses)]

# Each attribute takes a value from 0 to 4.
all_vars = names + food + car + phone + occ + drink
for var in all_vars:
    s.add(var >= 0, var < 5)

# All attributes are all-different per category.
s.add(Distinct(names))
s.add(Distinct(food))
s.add(Distinct(car))
s.add(Distinct(phone))
s.add(Distinct(occ))
s.add(Distinct(drink))

# Mappings (for our understanding):
# Names:  0:"Eric", 1:"Peter", 2:"Arnold", 3:"Alice", 4:"Bob"
# Food:   0:"stir fry", 1:"spaghetti", 2:"stew", 3:"grilled cheese", 4:"pizza"
# Car:    0:"ford f150", 1:"tesla model 3", 2:"bmw 3 series", 3:"toyota camry", 4:"honda civic"
# Phone:  0:"iphone 13", 1:"google pixel 6", 2:"samsung galaxy s21", 3:"oneplus 9", 4:"huawei p50"
# Occ:    0:"teacher", 1:"lawyer", 2:"doctor", 3:"artist", 4:"engineer"
# Drink:  0:"tea", 1:"milk", 2:"water", 3:"root beer", 4:"coffee"

# Helper: for equivalence constraints we add two implications.
def iff(a, b):
    return And(Implies(a, b), Implies(b, a))

# Clue 1: The root beer lover is the person who owns a Honda Civic.
for i in range(num_houses):
    s.add(iff(drink[i] == 3, car[i] == 4))

# Clue 2: The person who likes milk is directly left of the person who loves eating grilled cheese.
for i in range(num_houses - 1):
    s.add(Implies(drink[i] == 1, food[i+1] == 3))
for i in range(1, num_houses):
    s.add(Implies(food[i] == 3, drink[i-1] == 1))

# Clue 3: Alice is the person who uses a Samsung Galaxy S21.
for i in range(num_houses):
    s.add(Implies(names[i] == 3, phone[i] == 2))

# Clue 4: Alice is the person who loves stir fry.
for i in range(num_houses):
    s.add(Implies(names[i] == 3, food[i] == 0))

# Clue 5: The tea drinker is not in the fifth house.
s.add(drink[4] != 0)

# Clue 6: The person who owns a BMW 3 Series is somewhere to the left of the tea drinker.
for i in range(num_houses):
    for j in range(num_houses):
        s.add(Implies(And(car[i] == 2, drink[j] == 0), i < j))

# Clue 7: The person who is a doctor is Arnold.
for i in range(num_houses):
    s.add(Implies(names[i] == 2, occ[i] == 2))

# Clue 8: The person who uses an iPhone 13 is the coffee drinker.
for i in range(num_houses):
    s.add(iff(phone[i] == 0, drink[i] == 4))

# Clue 9: The person who is an engineer is the person who owns a BMW 3 Series.
for i in range(num_houses):
    s.add(iff(occ[i] == 4, car[i] == 2))

# Clue 10: The person who loves the stew is the person who uses an iPhone 13.
for i in range(num_houses):
    s.add(iff(food[i] == 2, phone[i] == 0))

# Clue 11: The person who is a doctor is directly left of the person who uses a OnePlus 9.
for i in range(num_houses - 1):
    s.add(Implies(occ[i] == 2, phone[i+1] == 3))
for i in range(1, num_houses):
    s.add(Implies(phone[i] == 3, occ[i-1] == 2))

# Clue 12: The person who owns a Honda Civic is directly left of the person who loves the spaghetti.
for i in range(num_houses - 1):
    s.add(Implies(car[i] == 4, food[i+1] == 1))
for i in range(1, num_houses):
    s.add(Implies(food[i] == 1, car[i-1] == 4))

# Clue 13: The person who uses a Google Pixel 6 is the tea drinker.
for i in range(num_houses):
    s.add(iff(phone[i] == 1, drink[i] == 0))

# Clue 14: Alice is the person who is an artist.
for i in range(num_houses):
    s.add(Implies(names[i] == 3, occ[i] == 3))

# Clue 15: There is one house between Alice and the person who owns a Ford F-150.
for i in range(num_houses):
    for j in range(num_houses):
        s.add(Implies(And(names[i] == 3, car[j] == 0), Or(i == j + 2, j == i + 2)))

# Clue 16: Arnold is the person who owns a Toyota Camry.
for i in range(num_houses):
    s.add(Implies(names[i] == 2, car[i] == 3))

# Clue 17: Eric is in the fourth house.
# (House numbering: 0-indexed house 3 is the fourth house.)
s.add(names[3] == 0)

# Clue 18: The person who uses a OnePlus 9 is the person who is a lawyer.
for i in range(num_houses):
    s.add(iff(phone[i] == 3, occ[i] == 1))

# Clue 19: The person who loves eating grilled cheese is Peter.
for i in range(num_houses):
    s.add(iff(food[i] == 3, names[i] == 1))

# Check for satisfiability and get a model.
if s.check() == sat:
    m = s.model()
    # Extract the solution in order of houses (house numbers 1 to 5)
    sol = []
    
    # Mappings to strings
    name_map = {0: "Eric", 1: "Peter", 2: "Arnold", 3: "Alice", 4: "Bob"}
    food_map = {0: "stir fry", 1: "spaghetti", 2: "stew", 3: "grilled cheese", 4: "pizza"}
    car_map  = {0: "ford f150", 1: "tesla model 3", 2: "bmw 3 series", 3: "toyota camry", 4: "honda civic"}
    phone_map = {0: "iphone 13", 1: "google pixel 6", 2: "samsung galaxy s21", 3: "oneplus 9", 4: "huawei p50"}
    occ_map   = {0: "teacher", 1: "lawyer", 2: "doctor", 3: "artist", 4: "engineer"}
    drink_map = {0: "tea", 1: "milk", 2: "water", 3: "root beer", 4: "coffee"}
    
    for i in range(num_houses):
        house_num = str(i+1)
        row = [
            house_num,
            name_map[m.evaluate(names[i]).as_long()],
            food_map[m.evaluate(food[i]).as_long()],
            car_map[m.evaluate(car[i]).as_long()],
            phone_map[m.evaluate(phone[i]).as_long()],
            occ_map[m.evaluate(occ[i]).as_long()],
            drink_map[m.evaluate(drink[i]).as_long()]
        ]
        sol.append(row)
    
    # Prepare final JSON dictionary
    import json
    result = {
        "solution": {
            "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
            "rows": sol
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found")