from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define the attributes
names = ["Eric", "Arnold", "Peter"]
phone_models = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
heights = ["very short", "average", "short"]
house_styles = ["colonial", "ranch", "victorian"]
car_models = ["tesla model 3", "toyota camry", "ford f150"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
phone = {h: String(f"phone_{h}") for h in houses}
height = {h: String(f"height_{h}") for h in houses}
style = {h: String(f"style_{h}") for h in houses}
car = {h: String(f"car_{h}") for h in houses}

# Add constraints that each attribute is one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([phone[h] == p for p in phone_models]))
    s.add(Or([height[h] == ht for ht in heights]))
    s.add(Or([style[h] == hs for hs in house_styles]))
    s.add(Or([car[h] == c for c in car_models]))

# Add uniqueness constraints
for attr in [name, phone, height, style, car]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Clue 1: Peter is somewhere to the right of Eric.
s.add(Exists([h1, h2], And(h1 < h2, name[h1] == "Eric", name[h2] == "Peter")))

# Clue 2: The person living in a colonial-style house is in the second house.
s.add(style[2] == "colonial")

# Clue 3: The person who owns a Tesla Model 3 is the person who is very short.
for h in houses:
    s.add(Implies(car[h] == "tesla model 3", height[h] == "very short"))

# Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
s.add(Or(
    And(height[1] == "short", phone[2] == "samsung galaxy s21"),
    And(height[2] == "short", phone[3] == "samsung galaxy s21")
))

# Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
s.add(Or(
    And(phone[1] == "iphone 13", phone[2] == "google pixel 6"),
    And(phone[2] == "iphone 13", phone[3] == "google pixel 6")
))

# Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
s.add(Exists([h1, h2], And(h1 < h2, style[h1] == "ranch", style[h2] == "colonial")))

# Clue 7: Arnold is in the second house.
s.add(name[2] == "Arnold")

# Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
s.add(Exists([h1, h2], And(h1 < h2, car[h1] == "toyota camry", car[h2] == "ford f150")))

# Clue 9: The person who has an average height is in the first house.
s.add(height[1] == "average")

# Check if the problem is satisfiable
if s.check() == sat:
    m = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            m.evaluate(name[h]).as_string(),
            m.evaluate(phone[h]).as_string(),
            m.evaluate(height[h]).as_string(),
            m.evaluate(style[h]).as_string(),
            m.evaluate(car[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")