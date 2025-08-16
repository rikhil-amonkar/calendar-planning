from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define the attributes
names = ['Eric', 'Peter', 'Arnold']
drinks = ['tea', 'water', 'milk']
nationalities = ['dane', 'brit', 'swede']
educations = ['high school', 'associate', 'bachelor']
house_styles = ['victorian', 'colonial', 'ranch']
smoothies = ['cherry', 'watermelon', 'desert']

# Create dictionaries to hold the variables for each attribute per house
name = {h: String(f'name_{h}') for h in houses}
drink = {h: String(f'drink_{h}') for h in houses}
nationality = {h: String(f'nationality_{h}') for h in houses}
education = {h: String(f'education_{h}') for h in houses}
house_style = {h: String(f'house_style_{h}') for h in houses}
smoothie = {h: String(f'smoothie_{h}') for h in houses}

# Add constraints that each attribute is unique per house
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([drink[h] for h in houses]))
s.add(Distinct([nationality[h] for h in houses]))
s.add(Distinct([education[h] for h in houses]))
s.add(Distinct([house_style[h] for h in houses]))
s.add(Distinct([smoothie[h] for h in houses]))

# Each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([drink[h] == d for d in drinks]))
    s.add(Or([nationality[h] == n for n in nationalities]))
    s.add(Or([education[h] == e for e in educations]))
    s.add(Or([house_style[h] == hs for hs in house_styles]))
    s.add(Or([smoothie[h] == sm for sm in smoothies]))

# Clue 1: There is one house between Eric and the tea drinker.
# This means if Eric is in house 1, tea is in house 3, or Eric in 2, tea in 4 (invalid), so only Eric in 1, tea in 3
s.add(Or(
    And(name[1] == 'Eric', drink[3] == 'tea'),
    And(name[2] == 'Eric', drink[1] == 'tea')  # But house 0 doesn't exist, so invalid
))
# So only valid possibility is Eric in 1, tea in 3
s.add(name[1] == 'Eric')
s.add(drink[3] == 'tea')

# Clue 2: The person who likes milk is the person in a ranch-style home.
for h in houses:
    s.add(Implies(drink[h] == 'milk', house_style[h] == 'ranch'))

# Clue 3: The person with a bachelor's degree is in the second house.
s.add(education[2] == 'bachelor')

# Clue 4: The person with a high school diploma is the Dane.
for h in houses:
    s.add(Implies(education[h] == 'high school', nationality[h] == 'dane'))

# Clue 5: The Desert smoothie lover is the Swedish person.
for h in houses:
    s.add(Implies(smoothie[h] == 'desert', nationality[h] == 'swede'))

# Clue 6: The person residing in a Victorian house is not in the first house.
s.add(Or(house_style[2] == 'victorian', house_style[3] == 'victorian'))

# Clue 7: The person who likes Cherry smoothies is the person living in a colonial-style house.
for h in houses:
    s.add(Implies(smoothie[h] == 'cherry', house_style[h] == 'colonial'))

# Clue 8: Arnold is somewhere to the right of the person residing in a Victorian house.
# So Victorian is left of Arnold
s.add(Or(
    And(house_style[1] == 'victorian', Or(name[2] == 'Arnold', name[3] == 'Arnold')),
    And(house_style[2] == 'victorian', name[3] == 'Arnold')
))

# Clue 9: The person in a ranch-style home is the person with a high school diploma.
for h in houses:
    s.add(Implies(house_style[h] == 'ranch', education[h] == 'high school'))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            str(m.evaluate(name[h])),
            str(m.evaluate(drink[h])),
            str(m.evaluate(nationality[h])),
            str(m.evaluate(education[h])),
            str(m.evaluate(house_style[h])),
            str(m.evaluate(smoothie[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")