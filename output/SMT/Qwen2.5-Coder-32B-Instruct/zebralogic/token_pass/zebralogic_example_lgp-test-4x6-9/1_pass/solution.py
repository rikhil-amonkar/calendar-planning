from z3 import *

# Create variables for each attribute for each house
names = [String(f'name_{i}') for i in range(4)]
flowers = [String(f'flower_{i}') for i in range(4)]
heights = [String(f'height_{i}') for i in range(4)]
mothers = [String(f'mother_{i}') for i in range(4)]
occupations = [String(f'occupation_{i}') for i in range(4)]
favorite_sports = [String(f'favorite_sport_{i}') for i in range(4)]

# Define the domain of each variable
possible_names = ['Peter', 'Arnold', 'Eric', 'Alice']
possible_flowers = ['daffodils', 'carnations', 'roses', 'lilies']
possible_heights = ['very short', 'short', 'tall', 'average']
possible_mothers = ['Janelle', 'Kailyn', 'Holly', 'Aniya']
possible_occupations = ['engineer', 'doctor', 'teacher', 'artist']
possible_favorite_sports = ['swimming', 'basketball', 'tennis', 'soccer']

# Create constraints for each variable to be in its domain
constraints = []
for var_list, possible_values in zip([names, flowers, heights, mothers, occupations, favorite_sports], 
                                    [possible_names, possible_flowers, possible_heights, possible_mothers, possible_occupations, possible_favorite_sports]):
    for var in var_list:
        constraints.append(Or([var == val for val in possible_values]))

# Add constraints based on the clues
# Clue 1: The person who loves swimming is the person who loves the rose bouquet.
constraints.append(Implies(favorite_sports[0] == 'swimming', flowers[0] == 'roses') |
                   Implies(favorite_sports[1] == 'swimming', flowers[1] == 'roses') |
                   Implies(favorite_sports[2] == 'swimming', flowers[2] == 'roses') |
                   Implies(favorite_sports[3] == 'swimming', flowers[3] == 'roses'))

# Clue 2: The person who loves the rose bouquet is Eric.
constraints.append(Implies(flowers[0] == 'roses', names[0] == 'Eric') |
                   Implies(flowers[1] == 'roses', names[1] == 'Eric') |
                   Implies(flowers[2] == 'roses', names[2] == 'Eric') |
                   Implies(flowers[3] == 'roses', names[3] == 'Eric'))

# Clue 3: Arnold is the person who is tall.
constraints.append(Implies(names[0] == 'Arnold', heights[0] == 'tall') |
                   Implies(names[1] == 'Arnold', heights[1] == 'tall') |
                   Implies(names[2] == 'Arnold', heights[2] == 'tall') |
                   Implies(names[3] == 'Arnold', heights[3] == 'tall'))

# Clue 4: The person who loves a bouquet of daffodils is somewhere to the right of the person who is an engineer.
constraints.append(Or(
    And(occupations[0] == 'engineer', Or(flowers[1] == 'daffodils', flowers[2] == 'daffodils', flowers[3] == 'daffodils')),
    And(occupations[1] == 'engineer', Or(flowers[2] == 'daffodils', flowers[3] == 'daffodils')),
    And(occupations[2] == 'engineer', flowers[3] == 'daffodils')
))

# Clue 5: The person who loves soccer is the person who is short.
constraints.append(Implies(favorite_sports[0] == 'soccer', heights[0] == 'short') |
                   Implies(favorite_sports[1] == 'soccer', heights[1] == 'short') |
                   Implies(favorite_sports[2] == 'soccer', heights[2] == 'short') |
                   Implies(favorite_sports[3] == 'soccer', heights[3] == 'short'))

# Clue 6: The person who is a teacher is in the first house.
constraints.append(occupations[0] == 'teacher')

# Clue 7: The person whose mother's name is Janelle is the person who loves a carnations arrangement.
constraints.append(Implies(mothers[0] == 'Janelle', flowers[0] == 'carnations') |
                   Implies(mothers[1] == 'Janelle', flowers[1] == 'carnations') |
                   Implies(mothers[2] == 'Janelle', flowers[2] == 'carnations') |
                   Implies(mothers[3] == 'Janelle', flowers[3] == 'carnations'))

# Clue 8: The person who loves basketball is the person who has an average height.
constraints.append(Implies(favorite_sports[0] == 'basketball', heights[0] == 'average') |
                   Implies(favorite_sports[1] == 'basketball', heights[1] == 'average') |
                   Implies(favorite_sports[2] == 'basketball', heights[2] == 'average') |
                   Implies(favorite_sports[3] == 'basketball', heights[3] == 'average'))

# Clue 9: Arnold is not in the third house.
constraints.append(names[2] != 'Arnold')

# Clue 10: The person whose mother's name is Holly is somewhere to the right of the person who has an average height.
constraints.append(Or(
    And(heights[0] == 'average', Or(mothers[1] == 'Holly', mothers[2] == 'Holly', mothers[3] == 'Holly')),
    And(heights[1] == 'average', Or(mothers[2] == 'Holly', mothers[3] == 'Holly')),
    And(heights[2] == 'average', mothers[3] == 'Holly')
))

# Clue 11: Peter is the person who is a doctor.
constraints.append(occupations[0] == 'doctor' | occupations[1] == 'doctor' | occupations[2] == 'doctor' | occupations[3] == 'doctor')

# Clue 12: The person whose mother's name is Aniya is Alice.
constraints.append(Implies(mothers[0] == 'Aniya', names[0] == 'Alice') |
                   Implies(mothers[1] == 'Aniya', names[1] == 'Alice') |
                   Implies(mothers[2] == 'Aniya', names[2] == 'Alice') |
                   Implies(mothers[3] == 'Aniya', names[3] == 'Alice'))

# Clue 13: Arnold is the person who loves the bouquet of lilies.
constraints.append(Implies(names[0] == 'Arnold', flowers[0] == 'lilies') |
                   Implies(names[1] == 'Arnold', flowers[1] == 'lilies') |
                   Implies(names[2] == 'Arnold', flowers[2] == 'lilies') |
                   Implies(names[3] == 'Arnold', flowers[3] == 'lilies'))

# All names, flowers, heights, mothers, occupations, and favorite sports must be unique
constraints.append(Distinct(names))
constraints.append(Distinct(flowers))
constraints.append(Distinct(heights))
constraints.append(Distinct(mothers))
constraints.append(Distinct(occupations))
constraints.append(Distinct(favorite_sports))

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
            "rows": []
        }
    }
    for i in range(4):
        house = str(i + 1)
        name = model[names[i]].as_string()[1:-1]
        flower = model[flowers[i]].as_string()[1:-1]
        height = model[heights[i]].as_string()[1:-1]
        mother = model[mothers[i]].as_string()[1:-1]
        occupation = model[occupations[i]].as_string()[1:-1]
        favorite_sport = model[favorite_sports[i]].as_string()[1:-1]
        solution["solution"]["rows"].append([house, name, flower, height, mother, occupation, favorite_sport])
    print(solution)
else:
    print("No solution found")