from z3 import *

# Create Solver
solver = Solver()

# Define Variables
names = ['Eric', 'Alice', 'Peter', 'Arnold']
smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
sports = ['soccer', 'tennis', 'basketball', 'swimming']
cars = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
flowers = ['daffodils', 'roses', 'lilies', 'carnations']

# Create Arrays for Each Attribute
house = [Int(f'house_{i}') for i in range(4)]
name = [String(f'name_{i}') for i in range(4)]
smoothie = [String(f'smoothie_{i}') for i in range(4)]
sport = [String(f'sport_{i}') for i in range(4)]
car = [String(f'car_{i}') for i in range(4)]
flower = [String(f'flower_{i}') for i in range(4)]

# Add Constraints for Unique Values per Attribute
for i in range(4):
    solver.add(house[i] == i + 1)
    solver.add(name[i] != name[(i+1) % 4])
    solver.add(smoothie[i] != smoothie[(i+1) % 4])
    solver.add(sport[i] != sport[(i+1) % 4])
    solver.add(car[i] != car[(i+1) % 4])
    solver.add(flower[i] != flower[(i+1) % 4])

# Add Domain Constraints
for i in range(4):
    solver.add(name[i] in names)
    solver.add(smoothie[i] in smoothies)
    solver.add(sport[i] in sports)
    solver.add(car[i] in cars)
    solver.add(flower[i] in flowers)

# Add Clue Constraints
solver.add(car[names.index('Eric')] == 'tesla model 3')
solver.add(flower[names.index('Eric')] == 'roses')
solver.add(smoothie[names.index('Peter')] == 'dragonfruit')
solver.add(smoothie[names.index('Arnold')] == 'desert')
solver.add(car[names.index('Arnold')] == 'toyota camry')
solver.add(sport[0] == 'tennis')
solver.add(abs(names.index('Arnold') - names.index(car.index('toyota camry'))) == 1)
solver.add(sport[names.index('Arnold')] == 'basketball')
solver.add(car[names.index('Arnold')] == 'toyota camry')
solver.add(flower[names.index(car.index('honda civic'))] == 'daffodils')
solver.add(car[names.index('Arnold')] == 'toyota camry')
solver.add(smoothie[names.index('Arnold')] == 'desert')
solver.add(flower[names.index('Arnold')] == 'lilies')
solver.add(smoothie[names.index('Arnold')] != 'watermelon')
solver.add(car.index('honda civic') > car.index('toyota camry'))
solver.add(flower[names.index('Arnold')] == 'lilies')
solver.add(abs(sports.index('tennis') - sports.index('soccer')) == 1)

# Solve the Problem
if solver.check() == sat:
    m = solver.model()
    solution = []
    for i in range(4):
        solution.append([
            str(i + 1),
            m[name[i]].as_string()[1:-1],  # Remove quotes from string
            m[smoothie[i]].as_string()[1:-1],
            m[sport[i]].as_string()[1:-1],
            m[car[i]].as_string()[1:-1],
            m[flower[i]].as_string()[1:-1]
        ])
    
    # Output the Solution in JSON Format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],' +
          f'"rows": {solution}' +
          '}'
          '}')
else:
    print("No solution found")