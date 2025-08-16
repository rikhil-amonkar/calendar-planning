from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3, 4]
names = ['Peter', 'Alice', 'Eric', 'Arnold']
mothers = ['Janelle', 'Holly', 'Aniya', 'Kailyn']
smoothies = ['watermelon', 'dragonfruit', 'desert', 'cherry']
heights = ['tall', 'average', 'short', 'very short']
educations = ['high school', 'associate', 'master', 'bachelor']

# Create dictionaries to map variables to their respective domains
name_vars = {house: Int(f'name_{house}') for house in houses}
mother_vars = {house: Int(f'mother_{house}') for house in houses}
smoothie_vars = {house: Int(f'smoothie_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}
education_vars = {house: Int(f'education_{house}') for house in houses}

# Add constraints for unique values within each category
for var_dict, domain in [(name_vars, names), (mother_vars, mothers), (smoothie_vars, smoothies), (height_vars, heights), (education_vars, educations)]:
    solver.add(Distinct([var_dict[house] for house in houses]))
    for house in houses:
        solver.add(var_dict[house] >= 0)
        solver.add(var_dict[house] < len(domain))

# Map values to integers for constraints
name_map = {name: i for i, name in enumerate(names)}
mother_map = {mother: i for i, mother in enumerate(mothers)}
smoothie_map = {smoothie: i for i, smoothie in enumerate(smoothies)}
height_map = {height: i for i, height in enumerate(heights)}
education_map = {education: i for i, education in enumerate(educations)}

# Add clues as constraints
# Clue 1
solver.add(mother_vars[3] == mother_map['Janelle'])

# Clue 2
solver.add(smoothie_vars[smoothie_map['desert']] == education_vars[education_map['master']])

# Clue 3
solver.add(smoothie_vars[1] != smoothie_map['desert'])

# Clue 4
solver.add(height_vars[height_map['very short']] < height_vars[height_map['high school']])

# Clue 5
solver.add(Or(
    And(name_vars[1] == name_map['Eric'], smoothie_vars[2] == smoothie_map['cherry']),
    And(name_vars[2] == name_map['Eric'], smoothie_vars[1] == smoothie_map['cherry']),
    And(name_vars[2] == name_map['Eric'], smoothie_vars[3] == smoothie_map['cherry']),
    And(name_vars[3] == name_map['Eric'], smoothie_vars[2] == smoothie_map['cherry']),
    And(name_vars[3] == name_map['Eric'], smoothie_vars[4] == smoothie_map['cherry']),
    And(name_vars[4] == name_map['Eric'], smoothie_vars[3] == smoothie_map['cherry'])
))

# Clue 6
solver.add(education_vars[3] != education_map['high school'])

# Clue 7
solver.add(mother_vars[mother_map['Kailyn']] == education_vars[education_map['associate']])

# Clue 8
solver.add(mother_vars[mother_map['Aniya']] == smoothie_vars[smoothie_map['cherry']])

# Clue 9
solver.add(height_vars[height_map['tall']] == mother_vars[mother_map['Janelle']])

# Clue 10
solver.add(name_vars[name_map['Arnold']] > height_vars[height_map['average']])

# Clue 11
solver.add(smoothie_vars[smoothie_map['dragonfruit']] + 1 == height_vars[height_map['short']])

# Clue 12
solver.add(name_vars[2] == name_map['Alice'])  # Since Alice is in the second house according to Clue 12

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        mother = mothers[model.evaluate(mother_vars[house]).as_long()]
        smoothie = smoothies[model.evaluate(smoothie_vars[house]).as_long()]
        height = heights[model.evaluate(height_vars[house]).as_long()]
        education = educations[model.evaluate(education_vars[house]).as_long()]
        solution.append([str(house), name, mother, smoothie, height, education])
    
    print({
        "solution": {
            "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
            "rows": solution
        }
    })
else:
    print("No solution found")