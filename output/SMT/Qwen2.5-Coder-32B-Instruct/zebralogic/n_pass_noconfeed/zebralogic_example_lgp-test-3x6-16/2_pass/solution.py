from z3 import *

# Define the domains
houses = [1, 2, 3]
names = ['Eric', 'Peter', 'Arnold']
drinks = ['tea', 'water', 'milk']
nationalities = ['dane', 'brit', 'swede']
educations = ['high school', 'associate', 'bachelor']
house_styles = ['victorian', 'colonial', 'ranch']
smoothies = ['cherry', 'watermelon', 'desert']

# Create variables
name_vars = {h: Int(f'name_{h}') for h in houses}
drink_vars = {h: Int(f'drink_{h}') for h in houses}
nationality_vars = {h: Int(f'nationality_{h}') for h in houses}
education_vars = {h: Int(f'education_{h}') for h in houses}
house_style_vars = {h: Int(f'house_style_{h}') for h in houses}
smoothie_vars = {h: Int(f'smoothie_{h}') for h in houses}

# Create solver
solver = Solver()

# Add domain constraints
for h in houses:
    solver.add(name_vars[h] >= 0, name_vars[h] < len(names))
    solver.add(drink_vars[h] >= 0, drink_vars[h] < len(drinks))
    solver.add(nationality_vars[h] >= 0, nationality_vars[h] < len(nationalities))
    solver.add(education_vars[h] >= 0, education_vars[h] < len(educations))
    solver.add(house_style_vars[h] >= 0, house_style_vars[h] < len(house_styles))
    solver.add(smoothie_vars[h] >= 0, smoothie_vars[h] < len(smoothies))

# All values must be distinct within their categories
solver.add(Distinct([name_vars[h] for h in houses]))
solver.add(Distinct([drink_vars[h] for h in houses]))
solver.add(Distinct([nationality_vars[h] for h in houses]))
solver.add(Distinct([education_vars[h] for h in houses]))
solver.add(Distinct([house_style_vars[h] for h in houses]))
solver.add(Distinct([smoothie_vars[h] for h in houses]))

# Clue 1: There is one house between Eric and the tea drinker.
eric_var = Int('eric')
tea_var = Int('tea')
solver.add(Or(And(eric_var == name_vars[1], tea_var == drink_vars[3]),
             And(eric_var == name_vars[2], tea_var == drink_vars[1]),
             And(eric_var == name_vars[3], tea_var == drink_vars[1])))

# Clue 2: The person who likes milk is the person in a ranch-style home.
for h in houses:
    solver.add(Implies(drink_vars[h] == drinks.index('milk'), 
                       house_style_vars[h] == house_styles.index('ranch')))

# Clue 3: The person with a bachelor's degree is in the second house.
solver.add(education_vars[2] == educations.index('bachelor'))

# Clue 4: The person with a high school diploma is the Dane.
dane_var = Int('dane')
high_school_var = Int('high_school')
solver.add(Or(And(dane_var == nationality_vars[1], high_school_var == education_vars[1]),
             And(dane_var == nationality_vars[2], high_school_var == education_vars[2]),
             And(dane_var == nationality_vars[3], high_school_var == education_vars[3])))

# Clue 5: The Desert smoothie lover is the Swedish person.
swede_var = Int('swede')
desert_var = Int('desert')
solver.add(Or(And(swede_var == nationality_vars[1], desert_var == smoothie_vars[1]),
             And(swede_var == nationality_vars[2], desert_var == smoothie_vars[2]),
             And(swede_var == nationality_vars[3], desert_var == smoothie_vars[3])))

# Clue 6: The person residing in a Victorian house is not in the first house.
solver.add(house_style_vars[1] != house_styles.index('victorian'))

# Clue 7: The person who likes Cherry smoothies is the person living in a colonial-style house.
cherry_var = Int('cherry')
colonial_var = Int('colonial')
solver.add(Or(And(cherry_var == smoothie_vars[1], colonial_var == house_style_vars[1]),
             And(cherry_var == smoothie_vars[2], colonial_var == house_style_vars[2]),
             And(cherry_var == smoothie_vars[3], colonial_var == house_style_vars[3])))

# Clue 8: Arnold is somewhere to the right of the person residing in a Victorian house.
victorian_var = Int('victorian')
arnold_var = Int('arnold')
solver.add(Or(And(victorian_var == house_style_vars[1], arnold_var == name_vars[2]),
             And(victorian_var == house_style_vars[1], arnold_var == name_vars[3]),
             And(victorian_var == house_style_vars[2], arnold_var == name_vars[3])))

# Clue 9: The person in a ranch-style home is the person with a high school diploma.
for h in houses:
    solver.add(Implies(house_style_vars[h] == house_styles.index('ranch'), 
                       education_vars[h] == educations.index('high school')))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
            "rows": []
        }
    }
    for h in houses:
        name = names[model[name_vars[h]].as_long()]
        drink = drinks[model[drink_vars[h]].as_long()]
        nationality = nationalities[model[nationality_vars[h]].as_long()]
        education = educations[model[education_vars[h]].as_long()]
        house_style = house_styles[model[house_style_vars[h]].as_long()]
        smoothie = smoothies[model[smoothie_vars[h]].as_long()]
        solution["solution"]["rows"].append([str(h), name, drink, nationality, education, house_style, smoothie])
    import json
    print(json.dumps(solution))
else:
    print("No solution found")