# Solve the logic puzzle using Z3 and print the required JSON structure

from z3 import Int, Distinct, And, Or, Solver
import json

# Houses are 1..3 (left to right)
HOUSES = [1, 2, 3]

# Define attribute values
names = ["Eric", "Peter", "Arnold"]
drinks = ["tea", "water", "milk"]
nationalities = ["dane", "brit", "swede"]
educations = ["high school", "associate", "bachelor"]
styles = ["victorian", "colonial", "ranch"]
smoothies = ["cherry", "watermelon", "desert"]

# Create Z3 Int variables for each attribute value representing its house index (1..3)
vars_by_category = {}

def mk_vars(category, values):
    d = {}
    for v in values:
        d[v] = Int(f"{category}_{v.replace(' ', '_')}")
    vars_by_category[category] = d
    return d

name_vars = mk_vars("Name", names)
drink_vars = mk_vars("Drink", drinks)
nat_vars   = mk_vars("Nationality", nationalities)
edu_vars   = mk_vars("Education", educations)
style_vars = mk_vars("HouseStyle", styles)
smooth_vars= mk_vars("Smoothie", smoothies)

s = Solver()

# Domain constraints: all variables in 1..3
for cat in vars_by_category.values():
    for v in cat.values():
        s.add(And(v >= 1, v <= 3))

# All-different within each category (each value occupies a unique house)
for cat in vars_by_category.values():
    s.add(Distinct(*cat.values()))

# Clues:

# 1. There is one house between Eric and the tea drinker.
s.add(Or(name_vars["Eric"] - drink_vars["tea"] == 2,
         drink_vars["tea"] - name_vars["Eric"] == 2))

# 2. The person who likes milk is the person in a ranch-style home.
s.add(drink_vars["milk"] == style_vars["ranch"])

# 3. The person with a bachelor's degree is in the second house.
s.add(edu_vars["bachelor"] == 2)

# 4. The person with a high school diploma is the Dane.
s.add(edu_vars["high school"] == nat_vars["dane"])

# 5. The Desert smoothie lover is the Swedish person.
s.add(smooth_vars["desert"] == nat_vars["swede"])

# 6. The person residing in a Victorian house is not in the first house.
s.add(style_vars["victorian"] != 1)

# 7. The person who likes Cherry smoothies is the person living in a colonial-style house.
s.add(smooth_vars["cherry"] == style_vars["colonial"])

# 8. Arnold is somewhere to the right of the person residing in a Victorian house.
s.add(name_vars["Arnold"] > style_vars["victorian"])

# 9. The person in a ranch-style home is the person with a high school diploma.
s.add(style_vars["ranch"] == edu_vars["high school"])

assert s.check().r == 1, "No solution found"

m = s.model()

# Helper to invert mapping: find which value in a category is at a given house
def value_at_house(cat_dict, house):
    for k, v in cat_dict.items():
        if m[v].as_long() == house:
            return k
    return None

header = ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"]
rows = []
for house in HOUSES:
    row = [
        str(house),
        value_at_house(name_vars, house),
        value_at_house(drink_vars, house),
        value_at_house(nat_vars, house),
        value_at_house(edu_vars, house),
        value_at_house(style_vars, house),
        value_at_house(smooth_vars, house),
    ]
    rows.append(row)

result = {
    "solution": {
        "header": header,
        "rows": rows
    }
}

print(json.dumps(result, ensure_ascii=False))