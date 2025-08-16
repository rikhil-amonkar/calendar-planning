from z3 import *
import json

# Mappings for each attribute.
# For names: 0: "Eric", 1: "Peter", 2: "Arnold"
name_str = {0: "Eric", 1: "Peter", 2: "Arnold"}
# For cigars: 0: "blue master", 1: "prince", 2: "pall mall"
cigar_str = {0: "blue master", 1: "prince", 2: "pall mall"}
# For hobbies: 0: "photography", 1: "gardening", 2: "cooking"
hobby_str = {0: "photography", 1: "gardening", 2: "cooking"}
# For educations: 0: "high school", 1: "associate", 2: "bachelor"
education_str = {0: "high school", 1: "associate", 2: "bachelor"}
# For drinks: 0: "tea", 1: "milk", 2: "water"
drink_str = {0: "tea", 1: "milk", 2: "water"}

# There are 3 houses: index 0,1,2 correspond to House 1,2,3 (from left to right).
houses = 3

# Define Z3 integer variables for each house attribute.
names = [Int(f"name_{i}") for i in range(houses)]
cigars = [Int(f"cigar_{i}") for i in range(houses)]
hobbies = [Int(f"hobby_{i}") for i in range(houses)]
educations = [Int(f"edu_{i}") for i in range(houses)]
drinks = [Int(f"drink_{i}") for i in range(houses)]

solver = Solver()

# All variables must be in the range 0..2 and be all different in their category.
for var_list in [names, cigars, hobbies, educations, drinks]:
    for var in var_list:
        solver.add(var >= 0, var <= 2)
    solver.add(Distinct(var_list))

# -----------------------------------------------------------------------------
# Clue 1: The person partial to Pall Mall is Peter.
# "pall mall" is cigar value 2 and "Peter" is name value 1.
for i in range(houses):
    solver.add(Implies(cigars[i] == 2, names[i] == 1))

# -----------------------------------------------------------------------------
# Clue 2: The person who likes milk is directly left of the person with a high school diploma.
# Milk is drink value 1 and high school is education value 0.
# Milk cannot be in the rightmost house.
solver.add(drinks[2] != 1)
# Enforce that either house 1 or house 2 (index 0 or 1) with milk has its immediate right neighbor with high school.
solver.add(Or(And(drinks[0] == 1, educations[1] == 0),
              And(drinks[1] == 1, educations[2] == 0)))

# -----------------------------------------------------------------------------
# Clue 3: Eric is the tea drinker.
# "Eric" is name value 0; "tea" is drink value 0.
for i in range(houses):
    solver.add(Implies(names[i] == 0, drinks[i] == 0))

# -----------------------------------------------------------------------------
# Clue 4: Arnold and the Prince smoker are next to each other.
# "Arnold" is name value 2; "prince" is cigar value 1.
conds = []
# Check both possible adjacent pairs.
conds.append(And(names[0] == 2, cigars[1] == 1))
conds.append(And(cigars[0] == 1, names[1] == 2))
conds.append(And(names[1] == 2, cigars[2] == 1))
conds.append(And(cigars[1] == 1, names[2] == 2))
solver.add(Or(conds))

# -----------------------------------------------------------------------------
# Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
# "gardening" is hobby value 1; "prince" is cigar value 1.
conds = []
conds.append(And(hobbies[0] == 1, cigars[1] == 1))
conds.append(And(hobbies[0] == 1, cigars[2] == 1))
conds.append(And(hobbies[1] == 1, cigars[2] == 1))
solver.add(Or(conds))

# -----------------------------------------------------------------------------
# Clue 6: The person who likes milk is the person with an associate's degree.
# Milk is drink value 1; "associate" is education value 1.
for i in range(houses):
    solver.add(Implies(drinks[i] == 1, educations[i] == 1))

# -----------------------------------------------------------------------------
# Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
# "bachelor" is education value 2; "photography" is hobby value 0.
solver.add(Or(And(educations[0] == 2, hobbies[1] == 0),
              And(educations[1] == 2, hobbies[2] == 0)))

# -----------------------------------------------------------------------------
# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    result_rows = []
    for i in range(houses):
        house_num = str(i + 1)
        name_val = name_str[model[names[i]].as_long()]
        cigar_val = cigar_str[model[cigars[i]].as_long()]
        hobby_val = hobby_str[model[hobbies[i]].as_long()]
        education_val = education_str[model[educations[i]].as_long()]
        drink_val = drink_str[model[drinks[i]].as_long()]
        result_rows.append([house_num, name_val, cigar_val, hobby_val, education_val, drink_val])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
            "rows": result_rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")