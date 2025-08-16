from z3 import *

# Create the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
house_styles = ["modern", "craftsman", "ranch", "victorian", "colonial"]
mothers = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
phone_models = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
drinks = ["coffee", "water", "root beer", "tea", "milk"]
animals = ["fish", "dog", "horse", "bird", "cat"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
house_style = {h: String(f"house_style_{h}") for h in houses}
mother = {h: String(f"mother_{h}") for h in houses}
phone_model = {h: String(f"phone_model_{h}") for h in houses}
drink = {h: String(f"drink_{h}") for h in houses}
animal = {h: String(f"animal_{h}") for h in houses}

# Add constraints that each attribute is one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([house_style[h] == hs for hs in house_styles]))
    s.add(Or([mother[h] == m for m in mothers]))
    s.add(Or([phone_model[h] == pm for pm in phone_models]))
    s.add(Or([drink[h] == d for d in drinks]))
    s.add(Or([animal[h] == a for a in animals]))

# Add uniqueness constraints
for attr in [name, house_style, mother, phone_model, drink, animal]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Add clues
# 1. The person who uses a Google Pixel 6 is not in the first house.
s.add(phone_model[1] != "google pixel 6")

# 2. The one who only drinks water is Alice.
for h in houses:
    s.add(Implies(drink[h] == "water", name[h] == "Alice"))

# 3. The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
h_huawei = [h for h in houses if phone_model[h] == "huawei p50"][0]
h_colonial = [h for h in houses if house_style[h] == "colonial"][0]
s.add(h_colonial > h_huawei)

# 4. The person who keeps horses is the person who uses a OnePlus 9.
for h in houses:
    s.add(Implies(animal[h] == "horse", phone_model[h] == "oneplus 9"))

# 5. The person in a ranch-style home is the person whose mother's name is Kailyn.
for h in houses:
    s.add(Implies(house_style[h] == "ranch", mother[h] == "Kailyn"))

# 6. The root beer lover is the cat lover.
for h in houses:
    s.add(Implies(drink[h] == "root beer", animal[h] == "cat"))

# 7. The person living in a colonial-style house is not in the fourth house.
s.add(house_style[4] != "colonial")

# 8. The bird keeper is in the fourth house.
s.add(animal[4] == "bird")

# 9. The tea drinker is Bob.
for h in houses:
    s.add(Implies(drink[h] == "tea", name[h] == "Bob"))

# 10. The tea drinker is somewhere to the right of the person whose mother's name is Kailyn.
h_kailyn = [h for h in houses if mother[h] == "Kailyn"][0]
h_tea = [h for h in houses if drink[h] == "tea"][0]
s.add(h_tea > h_kailyn)

# 11. The root beer lover is somewhere to the left of the person whose mother's name is Kailyn.
h_root_beer = [h for h in houses if drink[h] == "root beer"][0]
s.add(h_root_beer < h_kailyn)

# 12. The person who keeps horses is the person in a modern-style house.
for h in houses:
    s.add(Implies(animal[h] == "horse", house_style[h] == "modern"))

# 13. The person who uses an iPhone 13 is the person who likes milk.
for h in houses:
    s.add(Implies(phone_model[h] == "iphone 13", drink[h] == "milk"))

# 14. The dog owner is the person who likes milk.
for h in houses:
    s.add(Implies(animal[h] == "dog", drink[h] == "milk"))

# 15. The person who uses a Google Pixel 6 is the person in a Craftsman-style house.
for h in houses:
    s.add(Implies(phone_model[h] == "google pixel 6", house_style[h] == "craftsman"))

# 16. Eric is not in the second house.
s.add(name[2] != "Eric")

# 17. The tea drinker is in the fourth house.
s.add(drink[4] == "tea")

# 18. The person who keeps horses is in the third house.
s.add(animal[3] == "horse")

# 19. The person in a modern-style house is the person whose mother's name is Penny.
for h in houses:
    s.add(Implies(house_style[h] == "modern", mother[h] == "Penny"))

# 20. The root beer lover is Peter.
for h in houses:
    s.add(Implies(drink[h] == "root beer", name[h] == "Peter"))

# 21. The person whose mother's name is Aniya is not in the fourth house.
s.add(mother[4] != "Aniya")

# 22. The person whose mother's name is Janelle is the one who only drinks water.
for h in houses:
    s.add(Implies(mother[h] == "Janelle", drink[h] == "water"))

# Solve the problem
if s.check() == sat:
    m = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            m.eval(name[h]).as_string(),
            m.eval(house_style[h]).as_string(),
            m.eval(mother[h]).as_string(),
            m.eval(phone_model[h]).as_string(),
            m.eval(drink[h]).as_string(),
            m.eval(animal[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")