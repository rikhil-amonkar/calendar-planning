from z3 import *

# Define domains
names = ['Eric', 'Peter', 'Arnold']
drinks = ['tea', 'water', 'milk']
nationalities = ['dane', 'brit', 'swede']
educations = ['high school', 'associate', 'bachelor']
house_styles = ['victorian', 'colonial', 'ranch']
smoothies = ['cherry', 'watermelon', 'desert']

# Create variables for each house
name1, name2, name3 = Ints('name1 name2 name3')
drink1, drink2, drink3 = Ints('drink1 drink2 drink3')
nationality1, nationality2, nationality3 = Ints('nationality1 nationality2 nationality3')
education1, education2, education3 = Ints('education1 education2 education3')
house_style1, house_style2, house_style3 = Ints('house_style1 house_style2 house_style3')
smoothie1, smoothie2, smoothie3 = Ints('smoothie1 smoothie2 smoothie3')

# Create solver instance
solver = Solver()

# Add constraints for uniqueness within each characteristic
solver.add(Distinct(name1, name2, name3))
solver.add(Distinct(drink1, drink2, drink3))
solver.add(Distinct(nationality1, nationality2, nationality3))
solver.add(Distinct(education1, education2, education3))
solver.add(Distinct(house_style1, house_style2, house_style3))
solver.add(Distinct(smoothie1, smoothie2, smoothie3))

# Map values to integers for each domain
name_map = {name: i for i, name in enumerate(names)}
drink_map = {drink: i for i, drink in enumerate(drinks)}
nationality_map = {nationality: i for i, nationality in enumerate(nationalities)}
education_map = {education: i for i, education in enumerate(educations)}
house_style_map = {house_style: i for i, house_style in enumerate(house_styles)}
smoothie_map = {smoothie: i for i, smoothie in enumerate(smoothies)}

# Add constraints based on clues
# Clue 1: There is one house between Eric and the tea drinker.
solver.add(Or(
    And(name1 == name_map['Eric'], drink3 == drink_map['tea']),
    And(name3 == name_map['Eric'], drink1 == drink_map['tea'])
))

# Clue 2: The person who likes milk is the person in a ranch-style home.
solver.add(drink_map['milk'] == house_style_map['ranch'])

# Clue 3: The person with a bachelor's degree is in the second house.
solver.add(education2 == education_map['bachelor'])

# Clue 4: The person with a high school diploma is the Dane.
solver.add(And(education_map['high school'] == nationality_map['dane']))

# Clue 5: The Desert smoothie lover is the Swedish person.
solver.add(And(smoothie_map['desert'] == nationality_map['swede']))

# Clue 6: The person residing in a Victorian house is not in the first house.
solver.add(house_style1 != house_style_map['victorian'])

# Clue 7: The person who likes Cherry smoothies is the person living in a colonial-style house.
solver.add(And(smoothie_map['cherry'] == house_style_map['colonial']))

# Clue 8: Arnold is somewhere to the right of the person residing in a Victorian house.
solver.add(Or(
    And(name2 == name_map['Arnold'], house_style1 == house_style_map['victorian']),
    And(name3 == name_map['Arnold'], Or(house_style1 == house_style_map['victorian'], house_style2 == house_style_map['victorian']))
))

# Clue 9: The person in a ranch-style home is the person with a high school diploma.
solver.add(And(house_style_map['ranch'] == education_map['high school']))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    # Extract values from the model
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
            "rows": []
        }
    }
    for house in range(1, 4):
        name_val = names[model.eval(eval(f'name{house}')).as_long()]
        drink_val = drinks[model.eval(eval(f'drink{house}')).as_long()]
        nationality_val = nationalities[model.eval(eval(f'nationality{house}')).as_long()]
        education_val = educations[model.eval(eval(f'education{house}')).as_long()]
        house_style_val = house_styles[model.eval(eval(f'house_style{house}')).as_long()]
        smoothie_val = smoothies[model.eval(eval(f'smoothie{house}')).as_long()]
        solution["solution"]["rows"].append([str(house), name_val, drink_val, nationality_val, education_val, house_style_val, smoothie_val])
    print(solution)
else:
    print("No solution found")