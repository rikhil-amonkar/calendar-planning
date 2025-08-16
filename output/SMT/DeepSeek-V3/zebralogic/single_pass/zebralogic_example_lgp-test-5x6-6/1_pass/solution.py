from z3 import *

# Create the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
vacations = ["mountain", "city", "cruise", "beach", "camping"]
educations = ["doctorate", "high school", "bachelor", "associate", "master"]
colors = ["blue", "red", "white", "yellow", "green"]
phone_models = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
vacation = {h: String(f"vacation_{h}") for h in houses}
education = {h: String(f"education_{h}") for h in houses}
color = {h: String(f"color_{h}") for h in houses}
phone_model = {h: String(f"phone_model_{h}") for h in houses}
food = {h: String(f"food_{h}") for h in houses}

# Each attribute must be one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([vacation[h] == v for v in vacations]))
    s.add(Or([education[h] == e for e in educations]))
    s.add(Or([color[h] == c for c in colors]))
    s.add(Or([phone_model[h] == p for p in phone_models]))
    s.add(Or([food[h] == f for f in foods]))

# All attributes in each house must be unique
for attr in [name, vacation, education, color, phone_model, food]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Clue 1: The person who loves the stew is not in the first house.
s.add(food[1] != "stew")

# Clue 2: There are two houses between the person who loves stir fry and the person with an associate's degree.
for h in houses:
    if h + 3 <= 5:
        s.add(Implies(food[h] == "stir fry", education[h + 3] == "associate"))
    if h - 3 >= 1:
        s.add(Implies(education[h] == "associate", food[h - 3] == "stir fry"))

# Clue 3: The person who enjoys mountain retreats is the person with a bachelor's degree.
for h in houses:
    s.add(Implies(vacation[h] == "mountain", education[h] == "bachelor"))

# Clue 4: The person with a doctorate is somewhere to the right of Bob.
# First, find Bob's house and ensure doctorate is to the right
bob_house = Int("bob_house")
s.add(Or([And(name[h] == "Bob", bob_house == h) for h in houses]))
for h in houses:
    s.add(Implies(education[h] == "doctorate", h > bob_house))

# Clue 5: The person who uses a Samsung Galaxy S21 is in the third house.
s.add(phone_model[3] == "samsung galaxy s21")

# Clue 6: Eric is the person with a doctorate.
for h in houses:
    s.add(Implies(name[h] == "Eric", education[h] == "doctorate"))
    s.add(Implies(education[h] == "doctorate", name[h] == "Eric"))

# Clue 7: The person with a doctorate is in the third house.
s.add(education[3] == "doctorate")
s.add(name[3] == "Eric")

# Clue 8: The person who loves stir fry is the person with a bachelor's degree.
for h in houses:
    s.add(Implies(food[h] == "stir fry", education[h] == "bachelor"))
    s.add(Implies(education[h] == "bachelor", food[h] == "stir fry"))

# Clue 9: The person with a doctorate is the person who is a pizza lover.
s.add(food[3] == "pizza")

# Clue 10: The person whose favorite color is green is somewhere to the right of Peter.
# Find Peter's house and ensure green is to the right
peter_house = Int("peter_house")
s.add(Or([And(name[h] == "Peter", peter_house == h) for h in houses]))
for h in houses:
    s.add(Implies(color[h] == "green", h > peter_house))

# Clue 11: The person who enjoys camping trips is the person who uses an iPhone 13.
for h in houses:
    s.add(Implies(vacation[h] == "camping", phone_model[h] == "iphone 13"))
    s.add(Implies(phone_model[h] == "iphone 13", vacation[h] == "camping"))

# Clue 12: The person who likes going on cruises is Alice.
for h in houses:
    s.add(Implies(name[h] == "Alice", vacation[h] == "cruise"))
    s.add(Implies(vacation[h] == "cruise", name[h] == "Alice"))

# Clue 13: There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
# Samsung is in house 3, so high school is in house 1 or 3-2=1
s.add(education[1] == "high school")

# Clue 14: The person who uses a Google Pixel 6 is Arnold.
for h in houses:
    s.add(Implies(phone_model[h] == "google pixel 6", name[h] == "Arnold"))
    s.add(Implies(name[h] == "Arnold", phone_model[h] == "google pixel 6"))

# Clue 15: The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
# Find Huawei P50 house and OnePlus 9 is to the right
huawei_house = Int("huawei_house")
oneplus_house = Int("oneplus_house")
s.add(Or([And(phone_model[h] == "huawei p50", huawei_house == h) for h in houses]))
s.add(Or([And(phone_model[h] == "oneplus 9", oneplus_house == h) for h in houses]))
s.add(oneplus_house > huawei_house)

# Clue 16: Arnold is the person who loves eating grilled cheese.
for h in houses:
    s.add(Implies(name[h] == "Arnold", food[h] == "grilled cheese"))
    s.add(Implies(food[h] == "grilled cheese", name[h] == "Arnold"))

# Clue 17: The person who loves eating grilled cheese is not in the fourth house.
s.add(food[4] != "grilled cheese")

# Clue 18: There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
# bachelor is in h, red is in h+3
for h in houses:
    if h + 3 <= 5:
        s.add(Implies(education[h] == "bachelor", color[h + 3] == "red"))
    if h - 3 >= 1:
        s.add(Implies(color[h] == "red", education[h - 3] == "bachelor"))

# Clue 19: The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
# Find city house and beach is to the right
city_house = Int("city_house")
beach_house = Int("beach_house")
s.add(Or([And(vacation[h] == "city", city_house == h) for h in houses]))
s.add(Or([And(vacation[h] == "beach", beach_house == h) for h in houses]))
s.add(beach_house > city_house)

# Clue 20: The person whose favorite color is green is not in the second house.
s.add(color[2] != "green")

# Clue 21: The person who loves blue is somewhere to the right of Peter.
# Peter is in peter_house, blue is to the right
for h in houses:
    s.add(Implies(color[h] == "blue", h > peter_house))

# Clue 22: There is one house between the person who enjoys camping trips and the person who loves yellow.
# camping in h, yellow in h+2 or h-2
for h in houses:
    if h + 2 <= 5:
        s.add(Implies(vacation[h] == "camping", color[h + 2] == "yellow"))
    if h - 2 >= 1:
        s.add(Implies(color[h] == "yellow", vacation[h - 2] == "camping"))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            str(model.eval(name[h])),
            str(model.eval(vacation[h])),
            str(model.eval(education[h])),
            str(model.eval(color[h])),
            str(model.eval(phone_model[h])),
            str(model.eval(food[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")