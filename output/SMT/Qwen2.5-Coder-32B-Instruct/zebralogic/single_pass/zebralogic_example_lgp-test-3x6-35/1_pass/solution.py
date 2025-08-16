from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each attribute of each person
names = ['Eric', 'Arnold', 'Peter']
vacations = ['mountain', 'city', 'beach']
heights = ['very short', 'average', 'short']
flowers = ['carnations', 'daffodils', 'lilies']
hair_colors = ['brown', 'black', 'blonde']
educations = ['associate', 'bachelor', 'high school']

# Create dictionaries to hold the Z3 variables
house_vars = {}
for house in range(1, 4):
    house_vars[house] = {
        'name': Int(f'name_house_{house}'),
        'vacation': Int(f'vacation_house_{house}'),
        'height': Int(f'height_house_{house}'),
        'flower': Int(f'flower_house_{house}'),
        'hair_color': Int(f'hair_color_house_{house}'),
        'education': Int(f'education_house_{house}')
    }

# Add constraints for each attribute to be unique across houses
for attr in ['name', 'vacation', 'height', 'flower', 'hair_color', 'education']:
    solver.add(Distinct([house_vars[house][attr] for house in range(1, 4)]))

# Map string values to integer codes
name_map = {name: i for i, name in enumerate(names)}
vacation_map = {vacation: i for i, vacation in enumerate(vacations)}
height_map = {height: i for i, height in enumerate(heights)}
flower_map = {flower: i for i, flower in enumerate(flowers)}
hair_color_map = {hair_color: i for i, hair_color in enumerate(hair_colors)}
education_map = {education: i for i, education in enumerate(educations)}

# Add clues as constraints
# Clue 1: Peter is the person who has an average height.
solver.add(house_vars[1]['name'] != name_map['Peter'])
solver.add(house_vars[2]['name'] != name_map['Peter'])
solver.add(house_vars[3]['name'] != name_map['Peter'])
solver.add(Or(
    And(house_vars[1]['name'] == name_map['Peter'], house_vars[1]['height'] == height_map['average']),
    And(house_vars[2]['name'] == name_map['Peter'], house_vars[2]['height'] == height_map['average']),
    And(house_vars[3]['name'] == name_map['Peter'], house_vars[3]['height'] == height_map['average'])
))

# Clue 2: The person who loves a bouquet of daffodils is Arnold.
solver.add(Or(
    And(house_vars[1]['name'] == name_map['Arnold'], house_vars[1]['flower'] == flower_map['daffodils']),
    And(house_vars[2]['name'] == name_map['Arnold'], house_vars[2]['flower'] == flower_map['daffodils']),
    And(house_vars[3]['name'] == name_map['Arnold'], house_vars[3]['flower'] == flower_map['daffodils'])
))

# Clue 3: The person who is very short is not in the second house.
solver.add(house_vars[2]['height'] != height_map['very short'])

# Clue 4: The person who loves beach vacations is in the first house.
solver.add(house_vars[1]['vacation'] == vacation_map['beach'])

# Clue 5: The person with a high school diploma is in the third house.
solver.add(house_vars[3]['education'] == education_map['high school'])

# Clue 6: The person who is short is somewhere to the right of the person who is very short.
solver.add(Or(
    And(house_vars[1]['height'] == height_map['very short'], house_vars[2]['height'] == height_map['short']),
    And(house_vars[1]['height'] == height_map['very short'], house_vars[3]['height'] == height_map['short']),
    And(house_vars[2]['height'] == height_map['very short'], house_vars[3]['height'] == height_map['short'])
))

# Clue 7: The person who loves the boquet of lilies is Eric.
solver.add(Or(
    And(house_vars[1]['name'] == name_map['Eric'], house_vars[1]['flower'] == flower_map['lilies']),
    And(house_vars[2]['name'] == name_map['Eric'], house_vars[2]['flower'] == flower_map['lilies']),
    And(house_vars[3]['name'] == name_map['Eric'], house_vars[3]['flower'] == flower_map['lilies'])
))

# Clue 8: The person who loves the boquet of lilies is the person with a bachelor's degree.
solver.add(Or(
    And(house_vars[1]['flower'] == flower_map['lilies'], house_vars[1]['education'] == education_map['bachelor']),
    And(house_vars[2]['flower'] == flower_map['lilies'], house_vars[2]['education'] == education_map['bachelor']),
    And(house_vars[3]['flower'] == flower_map['lilies'], house_vars[3]['education'] == education_map['bachelor'])
))

# Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
solver.add(Or(
    And(house_vars[1]['name'] == name_map['Peter'], house_vars[2]['vacation'] == vacation_map['city']),
    And(house_vars[1]['name'] == name_map['Peter'], house_vars[3]['vacation'] == vacation_map['city']),
    And(house_vars[2]['name'] == name_map['Peter'], house_vars[3]['vacation'] == vacation_map['city'])
))

# Clue 10: The person who has blonde hair is in the third house.
solver.add(house_vars[3]['hair_color'] == hair_color_map['blonde'])

# Clue 11: The person who loves beach vacations is the person who has brown hair.
solver.add(Or(
    And(house_vars[1]['vacation'] == vacation_map['beach'], house_vars[1]['hair_color'] == hair_color_map['brown']),
    And(house_vars[2]['vacation'] == vacation_map['beach'], house_vars[2]['hair_color'] == hair_color_map['brown']),
    And(house_vars[3]['vacation'] == vacation_map['beach'], house_vars[3]['hair_color'] == hair_color_map['brown'])
))

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in range(1, 4):
        name = names[model.eval(house_vars[house]['name']).as_long()]
        vacation = vacations[model.eval(house_vars[house]['vacation']).as_long()]
        height = heights[model.eval(house_vars[house]['height']).as_long()]
        flower = flowers[model.eval(house_vars[house]['flower']).as_long()]
        hair_color = hair_colors[model.eval(house_vars[house]['hair_color']).as_long()]
        education = educations[model.eval(house_vars[house]['education']).as_long()]
        solution.append([str(house), name, vacation, height, flower, hair_color, education])
    
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],' +
          f'"rows": {solution}' +
          '}}')
else:
    print("No solution found")