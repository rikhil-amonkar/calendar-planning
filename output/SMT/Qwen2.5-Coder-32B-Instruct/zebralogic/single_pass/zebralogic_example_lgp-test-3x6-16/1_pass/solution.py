from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each characteristic
names = ['Eric', 'Peter', 'Arnold']
drinks = ['tea', 'water', 'milk']
nationalities = ['dane', 'brit', 'swede']
educations = ['high school', 'associate', 'bachelor']
house_styles = ['victorian', 'colonial', 'ranch']
smoothies = ['cherry', 'watermelon', 'desert']

# Create integer variables for each characteristic for each house
name_vars = [Int(f'name_{i+1}') for i in range(3)]
drink_vars = [Int(f'drink_{i+1}') for i in range(3)]
nationality_vars = [Int(f'nationality_{i+1}') for i in range(3)]
education_vars = [Int(f'education_{i+1}') for i in range(3)]
house_style_vars = [Int(f'house_style_{i+1}') for i in range(3)]
smoothie_vars = [Int(f'smoothie_{i+1}') for i in range(3)]

# Add constraints for unique values in each category
solver.add(Distinct(name_vars))
solver.add(Distinct(drink_vars))
solver.add(Distinct(nationality_vars))
solver.add(Distinct(education_vars))
solver.add(Distinct(house_style_vars))
solver.add(Distinct(smoothie_vars))

# Map names to integers
name_map = {name: i for i, name in enumerate(names)}
drink_map = {drink: i for i, drink in enumerate(drinks)}
nationality_map = {nationality: i for i, nationality in enumerate(nationalities)}
education_map = {education: i for i, education in enumerate(educations)}
house_style_map = {house_style: i for i, house_style in enumerate(house_styles)}
smoothie_map = {smoothie: i for i, smoothie in enumerate(smoothies)}

# Clue 1: There is one house between Eric and the tea drinker.
solver.add(Abs(name_vars[0] - drink_vars[0]) != 1)
solver.add(Abs(name_vars[0] - drink_vars[1]) == 1)
solver.add(Abs(name_vars[0] - drink_vars[2]) != 1)
solver.add(Abs(name_vars[1] - drink_vars[0]) != 1)
solver.add(Abs(name_vars[1] - drink_vars[1]) != 1)
solver.add(Abs(name_vars[1] - drink_vars[2]) == 1)
solver.add(Abs(name_vars[2] - drink_vars[0]) != 1)
solver.add(Abs(name_vars[2] - drink_vars[1]) == 1)
solver.add(Abs(name_vars[2] - drink_vars[2]) != 1)

# Clue 2: The person who likes milk is the person in a ranch-style home.
solver.add(drink_vars[i] == drink_map['milk'] for i in range(3) if house_style_vars[i] == house_style_map['ranch'])

# Clue 3: The person with a bachelor's degree is in the second house.
solver.add(education_vars[1] == education_map['bachelor'])

# Clue 4: The person with a high school diploma is the Dane.
solver.add(education_vars[i] == education_map['high school'] for i in range(3) if nationality_vars[i] == nationality_map['dane'])

# Clue 5: The Desert smoothie lover is the Swedish person.
solver.add(smoothie_vars[i] == smoothie_map['desert'] for i in range(3) if nationality_vars[i] == nationality_map['swede'])

# Clue 6: The person residing in a Victorian house is not in the first house.
solver.add(house_style_vars[0] != house_style_map['victorian'])

# Clue 7: The person who likes Cherry smoothies is the person living in a colonial-style house.
solver.add(smoothie_vars[i] == smoothie_map['cherry'] for i in range(3) if house_style_vars[i] == house_style_map['colonial'])

# Clue 8: Arnold is somewhere to the right of the person residing in a Victorian house.
solver.add(Or(
    And(house_style_vars[0] == house_style_map['victorian'], name_vars[1] == name_map['Arnold']),
    And(house_style_vars[0] == house_style_map['victorian'], name_vars[2] == name_map['Arnold']),
    And(house_style_vars[1] == house_style_map['victorian'], name_vars[2] == name_map['Arnold'])
))

# Clue 9: The person in a ranch-style home is the person with a high school diploma.
solver.add(education_vars[i] == education_map['high school'] for i in range(3) if house_style_vars[i] == house_style_map['ranch'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
            "rows": []
        }
    }
    for i in range(3):
        name = names[model.evaluate(name_vars[i]).as_long()]
        drink = drinks[model.evaluate(drink_vars[i]).as_long()]
        nationality = nationalities[model.evaluate(nationality_vars[i]).as_long()]
        education = educations[model.evaluate(education_vars[i]).as_long()]
        house_style = house_styles[model.evaluate(house_style_vars[i]).as_long()]
        smoothie = smoothies[model.evaluate(smoothie_vars[i]).as_long()]
        solution["solution"]["rows"].append([str(i+1), name, drink, nationality, education, house_style, smoothie])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")