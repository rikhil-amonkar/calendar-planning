from z3 import *

# Define variables
houses = [1, 2, 3, 4]
names = ['Peter', 'Eric', 'Alice', 'Arnold']
educations = ['bachelor', 'high school', 'associate', 'master']
music_genres = ['jazz', 'rock', 'pop', 'classical']
colors = ['green', 'red', 'yellow', 'white']
flowers = ['lilies', 'carnations', 'daffodils', 'roses']

# Create dictionaries to hold the Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
education_vars = {house: Int(f'education_{house}') for house in houses}
music_genre_vars = {house: Int(f'music_genre_{house}') for house in houses}
color_vars = {house: Int(f'color_{house}') for house in houses}
flower_vars = {house: Int(f'flower_{house}') for house in houses}

# Create a solver instance
solver = Solver()

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([education_vars[house] for house in houses]))
solver.add(Distinct([music_genre_vars[house] for house in houses]))
solver.add(Distinct([color_vars[house] for house in houses]))
solver.add(Distinct([flower_vars[house] for house in houses]))

# Map values to integers
name_map = {name: i for i, name in enumerate(names)}
education_map = {education: i for i, education in enumerate(educations)}
music_genre_map = {music_genre: i for i, music_genre in enumerate(music_genres)}
color_map = {color: i for i, color in enumerate(colors)}
flower_map = {flower: i for i, flower in enumerate(flowers)}

# Add constraints based on clues
# Clue 1
solver.add(education_vars[houses[0]] == education_map['bachelor'])
solver.add(flower_vars[houses[0]] == flower_map['daffodils'])

# Clue 2
solver.add(flower_vars[houses[0]] != flower_map['carnations'])
solver.add(flower_vars[houses[1]] != flower_map['carnations'])
solver.add(flower_vars[houses[2]] != flower_map['carnations'])

# Clue 3
solver.add(name_vars[houses[2]] == name_map['Alice'])
solver.add(education_vars[houses[2]] == education_map['master'])

# Clue 4
solver.add(music_genre_vars[houses[3]] == music_genre_map['classical'])

# Clue 5
solver.add(name_vars[houses[1]] != name_map['Eric'])

# Clue 6
solver.add(name_vars[houses[2]] != name_map['Arnold'])

# Clue 7
solver.add(color_vars[houses[0]] == color_map['yellow'])
solver.add(flower_vars[houses[1]] == flower_map['roses'])

# Clue 8
solver.add(music_genre_vars[houses[1]] == music_genre_map['pop'])

# Clue 9
solver.add(education_vars[houses[3]] != education_map['associate'])

# Clue 10
solver.add(flower_vars[houses[3]] != flower_map['carnations'])

# Clue 11
solver.add(color_vars[houses[0]] == color_map['red'])
solver.add(color_vars[houses[1]] == color_map['white'])

# Clue 12
solver.add(music_genre_vars[houses[0]] == music_genre_map['rock'])

# Clue 13
solver.add(color_vars[houses[0]] == color_map['yellow'])

# Clue 14
solver.add(flower_vars[houses[0]] == flower_map['daffodils'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        education = educations[model.evaluate(education_vars[house]).as_long()]
        music_genre = music_genres[model.evaluate(music_genre_vars[house]).as_long()]
        color = colors[model.evaluate(color_vars[house]).as_long()]
        flower = flowers[model.evaluate(flower_vars[house]).as_long()]
        solution.append([str(house), name, education, music_genre, color, flower])
    
    print({
        "solution": {
            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
            "rows": solution
        }
    })
else:
    print("No solution found")