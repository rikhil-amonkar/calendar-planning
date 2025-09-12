from z3 import *

# Define the domains
names = ['Peter', 'Eric', 'Alice', 'Arnold']
educations = ['bachelor', 'high school', 'associate', 'master']
music_genres = ['jazz', 'rock', 'pop', 'classical']
colors = ['green', 'red', 'yellow', 'white']
flowers = ['lilies', 'carnations', 'daffodils', 'roses']

# Create variables
house_vars = [Int(f'house_{i}') for i in range(1, 5)]
name_vars = {name: Int(f'name_{name}') for name in names}
education_vars = {edu: Int(f'education_{edu}') for edu in educations}
music_genre_vars = {genre: Int(f'music_genre_{genre}') for genre in music_genres}
color_vars = {color: Int(f'color_{color}') for color in colors}
flower_vars = {flower: Int(f'flower_{flower}') for flower in flowers}

# Create solver
solver = Solver()

# Add constraints for unique assignments
solver.add(Distinct(house_vars))
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(education_vars.values()))
solver.add(Distinct(music_genre_vars.values()))
solver.add(Distinct(color_vars.values()))
solver.add(Distinct(flower_vars.values()))

# Map names to houses
for name, var in name_vars.items():
    solver.add(Or([var == i for i in range(1, 5)]))

# Map educations to houses
for edu, var in education_vars.items():
    solver.add(Or([var == i for i in range(1, 5)]))

# Map music genres to houses
for genre, var in music_genre_vars.items():
    solver.add(Or([var == i for i in range(1, 5)]))

# Map colors to houses
for color, var in color_vars.items():
    solver.add(Or([var == i for i in range(1, 5)]))

# Map flowers to houses
for flower, var in flower_vars.items():
    solver.add(Or([var == i for i in range(1, 5)]))

# Add clues as constraints
solver.add(education_vars['bachelor'] == flower_vars['daffodils'])
solver.add(flower_vars['carnations'] != 1)
solver.add(education_vars['master'] == name_vars['Alice'])
solver.add(education_vars['master'] + 1 == music_genre_vars['classical'])
solver.add(name_vars['Eric'] != 2)
solver.add(name_vars['Arnold'] != 3)
solver.add(color_vars['yellow'] + 1 == flower_vars['roses'])
solver.add(music_genre_vars['pop'] == 2)
solver.add(education_vars['associate'] != 4)
solver.add(flower_vars['carnations'] != 4)
solver.add(color_vars['red'] + 1 == color_vars['white'])
solver.add(music_genre_vars['rock'] == color_vars['red'])
solver.add(color_vars['yellow'] == name_vars['Arnold'])
solver.add(flower_vars['daffodils'] == color_vars['yellow'])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in range(1, 5):
        name = next(name for name, var in name_vars.items() if model.evaluate(var) == house)
        education = next(edu for edu, var in education_vars.items() if model.evaluate(var) == house)
        music_genre = next(genre for genre, var in music_genre_vars.items() if model.evaluate(var) == house)
        color = next(color for color, var in color_vars.items() if model.evaluate(var) == house)
        flower = next(flower for flower, var in flower_vars.items() if model.evaluate(var) == house)
        solution.append([str(house), name, education, music_genre, color, flower])

    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
            "rows": solution
        }
    }))
else:
    print("No solution found")