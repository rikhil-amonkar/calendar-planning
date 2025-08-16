import json
from z3 import *

# Create the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
foods = ["stir fry", "spaghetti", "stew", "grilled cheese", "pizza"]
car_models = ["ford f150", "tesla model 3", "bmw 3 series", "toyota camry", "honda civic"]
phone_models = ["iphone 13", "google pixel 6", "samsung galaxy s21", "oneplus 9", "huawei p50"]
occupations = ["teacher", "lawyer", "doctor", "artist", "engineer"]
drinks = ["tea", "milk", "water", "root beer", "coffee"]

# Create variables for each attribute in each house
name = {h: Int(f"name_{h}") for h in houses}
food = {h: Int(f"food_{h}") for h in houses}
car = {h: Int(f"car_{h}") for h in houses}
phone = {h: Int(f"phone_{h}") for h in houses}
occupation = {h: Int(f"occupation_{h}") for h in houses}
drink = {h: Int(f"drink_{h}") for h in houses}

# Each attribute is between 0 and 4 (indexes of the lists)
for h in houses:
    s.add(And(name[h] >= 0, name[h] < 5))
    s.add(And(food[h] >= 0, food[h] < 5))
    s.add(And(car[h] >= 0, car[h] < 5))
    s.add(And(phone[h] >= 0, phone[h] < 5))
    s.add(And(occupation[h] >= 0, occupation[h] < 5))
    s.add(And(drink[h] >= 0, drink[h] < 5))

# All attributes in each category are distinct
for attr in [name, food, car, phone, occupation, drink]:
    s.add(Distinct([attr[h] for h in houses]))

# Clue 3: Alice is the person who uses a Samsung Galaxy S21
alice_idx = names.index("Alice")
samsung_idx = phone_models.index("samsung galaxy s21")
for h in houses:
    s.add(Implies(name[h] == alice_idx, phone[h] == samsung_idx))

# Clue 4: Alice is the person who loves stir fry
stir_fry_idx = foods.index("stir fry")
for h in houses:
    s.add(Implies(name[h] == alice_idx, food[h] == stir_fry_idx))

# Clue 14: Alice is the person who is an artist
artist_idx = occupations.index("artist")
for h in houses:
    s.add(Implies(name[h] == alice_idx, occupation[h] == artist_idx))

# Clue 15: There is one house between Alice and the person who owns a Ford F-150
ford_idx = car_models.index("ford f150")
for h in houses:
    if h + 2 <= 5:
        s.add(Implies(name[h] == alice_idx, car[h+2] == ford_idx))
    if h - 2 >= 1:
        s.add(Implies(name[h] == alice_idx, car[h-2] == ford_idx))

# Clue 17: Eric is in the fourth house
eric_idx = names.index("Eric")
s.add(name[4] == eric_idx)

# Clue 7: The person who is a doctor is Arnold
arnold_idx = names.index("Arnold")
doctor_idx = occupations.index("doctor")
for h in houses:
    s.add(Implies(occupation[h] == doctor_idx, name[h] == arnold_idx))

# Clue 16: Arnold is the person who owns a Toyota Camry
toyota_idx = car_models.index("toyota camry")
for h in houses:
    s.add(Implies(name[h] == arnold_idx, car[h] == toyota_idx))

# Clue 11: The person who is a doctor is directly left of the person who uses a OnePlus 9
oneplus_idx = phone_models.index("oneplus 9")
for h in houses:
    if h < 5:
        s.add(Implies(occupation[h] == doctor_idx, phone[h+1] == oneplus_idx))

# Clue 18: The person who uses a OnePlus 9 is the person who is a lawyer
lawyer_idx = occupations.index("lawyer")
for h in houses:
    s.add(Implies(phone[h] == oneplus_idx, occupation[h] == lawyer_idx))

# Clue 19: The person who loves eating grilled cheese is Peter
grilled_cheese_idx = foods.index("grilled cheese")
peter_idx = names.index("Peter")
for h in houses:
    s.add(Implies(food[h] == grilled_cheese_idx, name[h] == peter_idx))

# Clue 2: The person who likes milk is directly left of the person who loves eating grilled cheese
milk_idx = drinks.index("milk")
for h in houses:
    if h < 5:
        s.add(Implies(drink[h] == milk_idx, food[h+1] == grilled_cheese_idx))

# Clue 1: The root beer lover is the person who owns a Honda Civic
root_beer_idx = drinks.index("root beer")
honda_idx = car_models.index("honda civic")
for h in houses:
    s.add(Implies(drink[h] == root_beer_idx, car[h] == honda_idx))

# Clue 12: The person who owns a Honda Civic is directly left of the person who loves the spaghetti eater
spaghetti_idx = foods.index("spaghetti")
for h in houses:
    if h < 5:
        s.add(Implies(car[h] == honda_idx, food[h+1] == spaghetti_idx))

# Clue 5: The tea drinker is not in the fifth house
tea_idx = drinks.index("tea")
s.add(drink[5] != tea_idx)

# Clue 6: The person who owns a BMW 3 Series is somewhere to the left of the tea drinker
bmw_idx = car_models.index("bmw 3 series")
for h in houses:
    for h2 in houses:
        if h2 > h:
            s.add(Implies(car[h] == bmw_idx, drink[h2] == tea_idx))

# Clue 8: The person who uses an iPhone 13 is the coffee drinker
iphone_idx = phone_models.index("iphone 13")
coffee_idx = drinks.index("coffee")
for h in houses:
    s.add(Implies(phone[h] == iphone_idx, drink[h] == coffee_idx))

# Clue 9: The person who is an engineer is the person who owns a BMW 3 Series
engineer_idx = occupations.index("engineer")
for h in houses:
    s.add(Implies(occupation[h] == engineer_idx, car[h] == bmw_idx))

# Clue 10: The person who loves the stew is the person who uses an iPhone 13
stew_idx = foods.index("stew")
for h in houses:
    s.add(Implies(food[h] == stew_idx, phone[h] == iphone_idx))

# Clue 13: The person who uses a Google Pixel 6 is the tea drinker
pixel_idx = phone_models.index("google pixel 6")
for h in houses:
    s.add(Implies(phone[h] == pixel_idx, drink[h] == tea_idx))

# Solve the problem
if s.check() == sat:
    m = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
            "rows": []
        }
    }
    
    for h in houses:
        name_val = names[m.eval(name[h]).as_long()]
        food_val = foods[m.eval(food[h]).as_long()]
        car_val = car_models[m.eval(car[h]).as_long()]
        phone_val = phone_models[m.eval(phone[h]).as_long()]
        occupation_val = occupations[m.eval(occupation[h]).as_long()]
        drink_val = drinks[m.eval(drink[h]).as_long()]
        
        solution["solution"]["rows"].append([
            str(h),
            name_val,
            food_val,
            car_val,
            phone_val,
            occupation_val,
            drink_val
        ])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")