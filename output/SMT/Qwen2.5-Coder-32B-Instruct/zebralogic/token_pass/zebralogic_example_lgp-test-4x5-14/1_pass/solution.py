from z3 import *

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

# Create Z3 solver instance
solver = Solver()

# Add constraints for unique assignments
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([mother_vars[house] for house in houses]))
solver.add(Distinct([smoothie_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))
solver.add(Distinct([education_vars[house] for house in houses]))

# Map values to integers for Z3
name_map = {name: i for i, name in enumerate(names)}
mother_map = {mother: i for i, mother in enumerate(mothers)}
smoothie_map = {smoothie: i for i, smoothie in enumerate(smoothies)}
height_map = {height: i for i, height in enumerate(heights)}
education_map = {education: i for i, education in enumerate(educations)}

# Translate clues into constraints
# Clue 1
solver.add(mother_vars[3] == mother_map['Janelle'])

# Clue 2
solver.add(smoothie_vars[education_map['master']] == smoothie_map['desert'])

# Clue 3
solver.add(smoothie_vars[1] != smoothie_map['desert'])

# Clue 4
solver.add(height_vars[education_map['high school']] > height_vars[height_map['very short']])

# Clue 5
solver.add(Abs(name_vars[smoothie_map['cherry']] - name_vars[name_map['Eric']]) == 1)

# Clue 6
solver.add(education_vars[3] != education_map['high school'])

# Clue 7
solver.add(education_vars[mother_map['Kailyn']] == education_map['associate'])

# Clue 8
solver.add(mother_vars[smoothie_map['cherry']] == mother_map['Aniya'])

# Clue 9
solver.add(height_vars[mother_map['Janelle']] == height_map['tall'])

# Clue 10
solver.add(height_vars[name_map['Arnold']] > height_vars[height_map['average']])

# Clue 11
solver.add(height_vars[smoothie_map['cherry']] == height_vars[smoothie_map['dragonfruit']] + 1)

# Clue 12
solver.add(name_vars[height_map['tall']] == name_map['Alice'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        mother = mothers[model.evaluate(mother_vars[house]).as_long()]
        smoothie = smoothies[model.evaluate(smoothie_vars[house]).as_long()]
        height = heights[model.evaluate(height_vars[house]).as_long()]
        education = educations[model.evaluate(education_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, mother, smoothie, height, education])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")