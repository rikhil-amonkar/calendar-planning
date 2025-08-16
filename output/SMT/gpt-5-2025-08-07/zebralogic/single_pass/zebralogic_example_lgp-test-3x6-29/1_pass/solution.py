# Solve the logic puzzle with Z3 and print the solution as the required JSON
from z3 import Int, Distinct, Solver, And, sat
import json

def make_vars(category, values):
    return {val: Int(f"{category}_{val}") for val in values}

def domain_and_distinct(vars_dict, lo=1, hi=3):
    cons = []
    cons += [And(v >= lo, v <= hi) for v in vars_dict.values()]
    cons.append(Distinct(*vars_dict.values()))
    return cons

def attr_at_house(model, vars_dict, house):
    for k, v in vars_dict.items():
        if model.eval(v).as_long() == house:
            return k
    raise ValueError("No attribute found for house")

# Categories and values
Names = ["Arnold", "Peter", "Eric"]
Animals = ["bird", "horse", "cat"]
Birthdays = ["jan", "sept", "april"]
Hobbies = ["photography", "cooking", "gardening"]
Drinks = ["milk", "water", "tea"]
HairColors = ["black", "brown", "blonde"]

# Create Z3 variables for each value indicating the house number (1..3)
name_pos = make_vars("name", Names)
animal_pos = make_vars("animal", Animals)
birthday_pos = make_vars("birthday", Birthdays)
hobby_pos = make_vars("hobby", Hobbies)
drink_pos = make_vars("drink", Drinks)
hair_pos = make_vars("hair", HairColors)

s = Solver()

# Domain and distinct constraints for each category
for vars_dict in [name_pos, animal_pos, birthday_pos, hobby_pos, drink_pos, hair_pos]:
    s.add(*domain_and_distinct(vars_dict))

# Clues:
# 1. The person who has brown hair is the person who loves cooking.
s.add(hair_pos["brown"] == hobby_pos["cooking"])

# 2. The person whose birthday is in April is in the third house.
s.add(birthday_pos["april"] == 3)

# 3. Eric is not in the first house.
s.add(name_pos["Eric"] != 1)

# 4. The cat lover is in the second house.
s.add(animal_pos["cat"] == 2)

# 5. The person who has blonde hair is somewhere to the left of the person who likes milk.
s.add(hair_pos["blonde"] < drink_pos["milk"])

# 6. The person who enjoys gardening is the person who likes milk.
s.add(hobby_pos["gardening"] == drink_pos["milk"])

# 7. The cat lover is the person who has brown hair.
s.add(animal_pos["cat"] == hair_pos["brown"])

# 8. Arnold is the bird keeper.
s.add(name_pos["Arnold"] == animal_pos["bird"])

# 9. The one who only drinks water is the photography enthusiast.
s.add(drink_pos["water"] == hobby_pos["photography"])

# 10. The person whose birthday is in September is directly left of Arnold.
s.add(birthday_pos["sept"] + 1 == name_pos["Arnold"])

assert s.check() == sat, "Puzzle is unsatisfiable"
m = s.model()

# Build the output rows per house 1..3
rows = []
for h in [1, 2, 3]:
    row = [
        str(h),
        attr_at_house(m, name_pos, h),
        attr_at_house(m, animal_pos, h),
        attr_at_house(m, birthday_pos, h),
        attr_at_house(m, hobby_pos, h),
        attr_at_house(m, drink_pos, h),
        attr_at_house(m, hair_pos, h),
    ]
    rows.append(row)

result = {
    "solution": {
        "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
        "rows": rows
    }
}

print(json.dumps(result))