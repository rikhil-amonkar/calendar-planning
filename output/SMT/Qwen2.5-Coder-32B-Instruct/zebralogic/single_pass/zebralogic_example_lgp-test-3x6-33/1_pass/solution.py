from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3]
names = ['Arnold', 'Eric', 'Peter']
flowers = ['carnations', 'lilies', 'daffodils']
hair_colors = ['black', 'brown', 'blonde']
favorite_sports = ['soccer', 'basketball', 'tennis']
house_styles = ['colonial', 'ranch', 'victorian']
pets = ['fish', 'dog', 'cat']

# Create dictionaries to hold the variables
name_vars = {house: Int(f'name_{house}') for house in houses}
flower_vars = {house: Int(f'flower_{house}') for house in houses}
hair_color_vars = {house: Int(f'hair_color_{house}') for house in houses}
favorite_sport_vars = {house: Int(f'favorite_sport_{house}') for house in houses}
house_style_vars = {house: Int(f'house_style_{house}') for house in houses}
pet_vars = {house: Int(f'pet_{house}') for house in houses}

# Add constraints for unique values within each category
for house in houses:
    solver.add(name_vars[house] >= 0)
    solver.add(name_vars[house] < len(names))
    solver.add(flower_vars[house] >= 0)
    solver.add(flower_vars[house] < len(flowers))
    solver.add(hair_color_vars[house] >= 0)
    solver.add(hair_color_vars[house] < len(hair_colors))
    solver.add(favorite_sport_vars[house] >= 0)
    solver.add(favorite_sport_vars[house] < len(favorite_sports))
    solver.add(house_style_vars[house] >= 0)
    solver.add(house_style_vars[house] < len(house_styles))
    solver.add(pet_vars[house] >= 0)
    solver.add(pet_vars[house] < len(pets))

# Ensure uniqueness across houses
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([flower_vars[house] for house in houses]))
solver.add(Distinct([hair_color_vars[house] for house in houses]))
solver.add(Distinct([favorite_sport_vars[house] for house in houses]))
solver.add(Distinct([house_style_vars[house] for house in houses]))
solver.add(Distinct([pet_vars[house] for house in houses]))

# Add clues as constraints
# 1. The person who has a cat is the person who loves soccer.
solver.add(Implies(pet_vars[3] == pets.index('cat'), favorite_sport_vars[3] == favorite_sports.index('soccer')))
solver.add(Implies(favorite_sport_vars[3] == favorite_sports.index('soccer'), pet_vars[3] == pets.index('cat')))

# 2. The person who has blonde hair is in the second house.
solver.add(hair_color_vars[2] == hair_colors.index('blonde'))

# 3. The person who loves a bouquet of daffodils is the person who has blonde hair.
solver.add(flower_vars[2] == flowers.index('daffodils'))

# 4. Peter is the person who loves basketball.
solver.add(And(name_vars[house] == names.index('Peter'), favorite_sport_vars[house] == favorite_sports.index('basketball')) for house in houses)

# 5. Arnold is directly left of the person in a ranch-style home.
solver.add(Or(
    And(name_vars[1] == names.index('Arnold'), house_style_vars[2] == house_styles.index('ranch')),
    And(name_vars[2] == names.index('Arnold'), house_style_vars[3] == house_styles.index('ranch'))
))

# 6. The person who owns a dog is the person who loves basketball.
solver.add(Implies(pet_vars[house] == pets.index('dog'), favorite_sport_vars[house] == favorite_sports.index('basketball')) for house in houses)

# 7. The person who loves a carnations arrangement is directly left of the person who has blonde hair.
solver.add(flower_vars[1] == flowers.index('carnations'))

# 8. The person who loves soccer is in the third house.
solver.add(favorite_sport_vars[3] == favorite_sports.index('soccer'))

# 9. Arnold is somewhere to the left of the person who has black hair.
solver.add(Or(
    And(name_vars[1] == names.index('Arnold'), hair_color_vars[2] == hair_colors.index('black')),
    And(name_vars[1] == names.index('Arnold'), hair_color_vars[3] == hair_colors.index('black')),
    And(name_vars[2] == names.index('Arnold'), hair_color_vars[3] == hair_colors.index('black'))
))

# 10. The person living in a colonial-style house is in the third house.
solver.add(house_style_vars[3] == house_styles.index('colonial'))

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        flower = flowers[model[flower_vars[house]].as_long()]
        hair_color = hair_colors[model[hair_color_vars[house]].as_long()]
        favorite_sport = favorite_sports[model[favorite_sport_vars[house]].as_long()]
        house_style = house_styles[model[house_style_vars[house]].as_long()]
        pet = pets[model[pet_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, flower, hair_color, favorite_sport, house_style, pet])
    print(json.dumps(solution, indent=4))
else:
    print("No solution found")