import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define the attributes
names = ['Eric', 'Peter', 'Arnold']
drinks = ['milk', 'water', 'tea']
vacations = ['mountain', 'city', 'beach']
house_styles = ['colonial', 'victorian', 'ranch']
animals = ['cat', 'bird', 'horse']
birthdays = ['jan', 'sept', 'april']

# Create variables for each attribute in each house
name = {h: String(f'name_{h}') for h in houses}
drink = {h: String(f'drink_{h}') for h in houses}
vacation = {h: String(f'vacation_{h}') for h in houses}
house_style = {h: String(f'house_style_{h}') for h in houses}
animal = {h: String(f'animal_{h}') for h in houses}
birthday = {h: String(f'birthday_{h}') for h in houses}

# Add constraints that each attribute is unique across houses
for attr in [name, drink, vacation, house_style, animal, birthday]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([drink[h] == d for d in drinks]))
    s.add(Or([vacation[h] == v for v in vacations]))
    s.add(Or([house_style[h] == hs for hs in house_styles]))
    s.add(Or([animal[h] == a for a in animals]))
    s.add(Or([birthday[h] == b for b in birthdays]))

# Apply the clues
# 1. The person living in a colonial-style house is somewhere to the left of the person who likes milk.
s.add(Or(
    And(house_style[1] == 'colonial', Or(drink[2] == 'milk', drink[3] == 'milk')),
    And(house_style[2] == 'colonial', drink[3] == 'milk')
))

# 2. The person who prefers city breaks is directly left of the person residing in a Victorian house.
s.add(Or(
    And(vacation[1] == 'city', house_style[2] == 'victorian'),
    And(vacation[2] == 'city', house_style[3] == 'victorian')
))

# 3. The person whose birthday is in January is directly left of the cat lover.
s.add(Or(
    And(birthday[1] == 'jan', animal[2] == 'cat'),
    And(birthday[2] == 'jan', animal[3] == 'cat')
))

# 4. The one who only drinks water is the person who enjoys mountain retreats.
for h in houses:
    s.add(Implies(drink[h] == 'water', vacation[h] == 'mountain'))

# 5. The person who keeps horses is Peter.
for h in houses:
    s.add(Implies(animal[h] == 'horse', name[h] == 'Peter'))

# 6. The person residing in a Victorian house is somewhere to the right of the person who loves beach vacations.
s.add(Or(
    And(vacation[1] == 'beach', Or(house_style[2] == 'victorian', house_style[3] == 'victorian')),
    And(vacation[2] == 'beach', house_style[3] == 'victorian')
))

# 7. Peter is the person who prefers city breaks.
for h in houses:
    s.add(Implies(name[h] == 'Peter', vacation[h] == 'city'))

# 8. The person who enjoys mountain retreats is the person whose birthday is in April.
for h in houses:
    s.add(Implies(vacation[h] == 'mountain', birthday[h] == 'april'))

# 9. Eric is the one who only drinks water.
for h in houses:
    s.add(Implies(name[h] == 'Eric', drink[h] == 'water'))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
            "rows": []
        }
    }
    for h in sorted(houses):
        row = [
            str(h),
            str(model.eval(name[h])),
            str(model.eval(drink[h])),
            str(model.eval(vacation[h])),
            str(model.eval(house_style[h])),
            str(model.eval(animal[h])),
            str(model.eval(birthday[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")