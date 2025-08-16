from z3 import *
import json

# Define EnumSorts
Name, (Eric, Peter, Arnold, Alice, Bob) = EnumSort('Name', ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob'])
Food, (stir_fry, spaghetti, stew, grilled_cheese, pizza) = EnumSort('Food', ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza'])
Car, (ford_f150, tesla_model_3, bmw_3_series, toyota_camry, honda_civic) = EnumSort('Car', ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic'])
Phone, (iphone_13, google_pixel_6, samsung_galaxy_s21, oneplus_9, huawei_p50) = EnumSort('Phone', ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50'])
Occupation, (teacher, lawyer, doctor, artist, engineer) = EnumSort('Occupation', ['teacher', 'lawyer', 'doctor', 'artist', 'engineer'])
Drink, (tea, milk, water, root_beer, coffee) = EnumSort('Drink', ['tea', 'milk', 'water', 'root beer', 'coffee'])

s = Solver()

# Create variables for each house (1-5)
name = [Const(f'name_{i}', Name) for i in range(1, 6)]
food = [Const(f'food_{i}', Food) for i in range(1, 6)]
car = [Const(f'car_{i}', Car) for i in range(1, 6)]
phone = [Const(f'phone_{i}', Phone) for i in range(1, 6)]
occupation = [Const(f'occupation_{i}', Occupation) for i in range(1, 6)]
drink = [Const(f'drink_{i}', Drink) for i in range(1, 6)]

# Add distinct constraints
s.add(Distinct(name))
s.add(Distinct(food))
s.add(Distinct(car))
s.add(Distinct(phone))
s.add(Distinct(occupation))
s.add(Distinct(drink))

# Add clues as constraints
# Clue 1: root beer lover owns Honda Civic
for i in range(5):
    s.add(Implies(drink[i] == root_beer, car[i] == honda_civic))

# Clue 2: milk drinker directly left of grilled cheese
clue2 = Or([And(drink[i] == milk, food[i+1] == grilled_cheese) for i in range(4)])
s.add(clue2)

# Clue 3: Alice uses Samsung Galaxy S21
for i in range(5):
    s.add(Implies(name[i] == Alice, phone[i] == samsung_galaxy_s21))

# Clue 4: Alice loves stir fry
for i in range(5):
    s.add(Implies(name[i] == Alice, food[i] == stir_fry))

# Clue 5: Tea drinker not in house 5
s.add(drink[4] != tea)

# Clue 6: BMW 3 Series is left of tea drinker
for i in range(5):
    for j in range(5):
        s.add(Implies(And(car[i] == bmw_3_series, drink[j] == tea), i < j))

# Clue 7: Arnold is doctor
for i in range(5):
    s.add(Implies(name[i] == Arnold, occupation[i] == doctor))

# Clue 8: iPhone 13 user drinks coffee
for i in range(5):
    s.add(Implies(phone[i] == iphone_13, drink[i] == coffee))

# Clue 9: Engineer owns BMW 3 Series
for i in range(5):
    s.add(Implies(occupation[i] == engineer, car[i] == bmw_3_series))

# Clue 10: Stew lover uses iPhone 13
for i in range(5):
    s.add(Implies(food[i] == stew, phone[i] == iphone_13))

# Clue 11: Doctor directly left of OnePlus 9 user
for i in range(4):
    s.add(Implies(occupation[i] == doctor, phone[i+1] == oneplus_9))

# Clue 12: Honda Civic directly left of spaghetti
for i in range(4):
    s.add(Implies(car[i] == honda_civic, food[i+1] == spaghetti))

# Clue 13: Google Pixel 6 user drinks tea
for i in range(5):
    s.add(Implies(phone[i] == google_pixel_6, drink[i] == tea))

# Clue 14: Alice is artist
for i in range(5):
    s.add(Implies(name[i] == Alice, occupation[i] == artist))

# Clue 15: One house between Alice and Ford F-150
for i in range(5):
    for j in range(5):
        s.add(Implies(And(name[i] == Alice, car[j] == ford_f150), Abs(i - j) == 2))

# Clue 16: Arnold owns Toyota Camry
for i in range(5):
    s.add(Implies(name[i] == Arnold, car[i] == toyota_camry))

# Clue 17: Eric is in house 4
s.add(name[3] == Eric)

# Clue 18: OnePlus 9 user is lawyer
for i in range(5):
    s.add(Implies(phone[i] == oneplus_9, occupation[i] == lawyer))

# Clue 19: Grilled cheese lover is Peter
for i in range(5):
    s.add(Implies(food[i] == grilled_cheese, name[i] == Peter))

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
            "rows": []
        }
    }
    for i in range(5):
        house_num = i + 1
        n = model[name[i]].decl().name()
        f = model[food[i]].decl().name().replace('_', ' ')
        c = model[car[i]].decl().name().replace('_', ' ')
        p = model[phone[i]].decl().name().replace('_', ' ')
        o = model[occupation[i]].decl().name()
        d = model[drink[i]].decl().name().replace('_', ' ')
        solution["solution"]["rows"].append([str(house_num), n, f, c, p, o, d])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")