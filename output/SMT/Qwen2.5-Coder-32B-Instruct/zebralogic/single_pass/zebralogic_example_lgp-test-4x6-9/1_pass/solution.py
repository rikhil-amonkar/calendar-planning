from z3 import *

# Create Solver instance
solver = Solver()

# Define variables
names = ['Peter', 'Arnold', 'Eric', 'Alice']
flowers = ['daffodils', 'carnations', 'roses', 'lilies']
heights = ['very short', 'short', 'tall', 'average']
mothers = ['Janelle', 'Kailyn', 'Holly', 'Aniya']
occupations = ['engineer', 'doctor', 'teacher', 'artist']
sports = ['swimming', 'basketball', 'tennis', 'soccer']

# Create arrays for each attribute
house_names = [String(f'name_{i}') for i in range(1, 5)]
house_flowers = [String(f'flower_{i}') for i in range(1, 5)]
house_heights = [String(f'height_{i}') for i in range(1, 5)]
house_mothers = [String(f'mother_{i}') for i in range(1, 5)]
house_occupations = [String(f'occupation_{i}') for i in range(1, 5)]
house_sports = [String(f'sport_{i}') for i in range(1, 5)]

# Add constraints for unique values within each category
solver.add(Distinct(house_names))
solver.add(Distinct(house_flowers))
solver.add(Distinct(house_heights))
solver.add(Distinct(house_mothers))
solver.add(Distinct(house_occupations))
solver.add(Distinct(house_sports))

# Add domain constraints
for h in range(4):
    solver.add(Or([house_names[h] == n for n in names]))
    solver.add(Or([house_flowers[h] == f for f in flowers]))
    solver.add(Or([house_heights[h] == ht for ht in heights]))
    solver.add(Or([house_mothers[h] == m for m in mothers]))
    solver.add(Or([house_occupations[h] == oc for oc in occupations]))
    solver.add(Or([house_sports[h] == s for s in sports]))

# Add specific clues
# 1. The person who loves swimming is the person who loves the rose bouquet.
solver.add(Implies(house_sports[0] == 'swimming', house_flowers[0] == 'roses'))
solver.add(Implies(house_sports[1] == 'swimming', house_flowers[1] == 'roses'))
solver.add(Implies(house_sports[2] == 'swimming', house_flowers[2] == 'roses'))
solver.add(Implies(house_sports[3] == 'swimming', house_flowers[3] == 'roses'))

# 2. The person who loves the rose bouquet is Eric.
solver.add(house_flowers[0] == 'roses' >> house_names[0] == 'Eric')
solver.add(house_flowers[1] == 'roses' >> house_names[1] == 'Eric')
solver.add(house_flowers[2] == 'roses' >> house_names[2] == 'Eric')
solver.add(house_flowers[3] == 'roses' >> house_names[3] == 'Eric')

# 3. Arnold is the person who is tall.
solver.add(Implies(house_names[0] == 'Arnold', house_heights[0] == 'tall'))
solver.add(Implies(house_names[1] == 'Arnold', house_heights[1] == 'tall'))
solver.add(Implies(house_names[2] == 'Arnold', house_heights[2] == 'tall'))
solver.add(Implies(house_names[3] == 'Arnold', house_heights[3] == 'tall'))

# 4. The person who loves a bouquet of daffodils is somewhere to the right of the person who is an engineer.
solver.add(Or(
    And(house_flowers[1] == 'daffodils', house_occupations[0] == 'engineer'),
    And(house_flowers[2] == 'daffodils', Or(house_occupations[0] == 'engineer', house_occupations[1] == 'engineer')),
    And(house_flowers[3] == 'daffodils', Or(house_occupations[0] == 'engineer', house_occupations[1] == 'engineer', house_occupations[2] == 'engineer'))
))

# 5. The person who loves soccer is the person who is short.
solver.add(Implies(house_sports[0] == 'soccer', house_heights[0] == 'short'))
solver.add(Implies(house_sports[1] == 'soccer', house_heights[1] == 'short'))
solver.add(Implies(house_sports[2] == 'soccer', house_heights[2] == 'short'))
solver.add(Implies(house_sports[3] == 'soccer', house_heights[3] == 'short'))

# 6. The person who is a teacher is in the first house.
solver.add(house_occupations[0] == 'teacher')

# 7. The person whose mother's name is Janelle is the person who loves a carnations arrangement.
solver.add(Implies(house_mothers[0] == 'Janelle', house_flowers[0] == 'carnations'))
solver.add(Implies(house_mothers[1] == 'Janelle', house_flowers[1] == 'carnations'))
solver.add(Implies(house_mothers[2] == 'Janelle', house_flowers[2] == 'carnations'))
solver.add(Implies(house_mothers[3] == 'Janelle', house_flowers[3] == 'carnations'))

# 8. The person who loves basketball is the person who has an average height.
solver.add(Implies(house_sports[0] == 'basketball', house_heights[0] == 'average'))
solver.add(Implies(house_sports[1] == 'basketball', house_heights[1] == 'average'))
solver.add(Implies(house_sports[2] == 'basketball', house_heights[2] == 'average'))
solver.add(Implies(house_sports[3] == 'basketball', house_heights[3] == 'average'))

# 9. Arnold is not in the third house.
solver.add(house_names[2] != 'Arnold')

# 10. The person whose mother's name is Holly is somewhere to the right of the person who has an average height.
solver.add(Or(
    And(house_mothers[1] == 'Holly', house_heights[0] == 'average'),
    And(house_mothers[2] == 'Holly', Or(house_heights[0] == 'average', house_heights[1] == 'average')),
    And(house_mothers[3] == 'Holly', Or(house_heights[0] == 'average', house_heights[1] == 'average', house_heights[2] == 'average'))
))

# 11. Peter is the person who is a doctor.
solver.add(Implies(house_names[0] == 'Peter', house_occupations[0] == 'doctor'))
solver.add(Implies(house_names[1] == 'Peter', house_occupations[1] == 'doctor'))
solver.add(Implies(house_names[2] == 'Peter', house_occupations[2] == 'doctor'))
solver.add(Implies(house_names[3] == 'Peter', house_occupations[3] == 'doctor'))

# 12. The person whose mother's name is Aniya is Alice.
solver.add(Implies(house_mothers[0] == 'Aniya', house_names[0] == 'Alice'))
solver.add(Implies(house_mothers[1] == 'Aniya', house_names[1] == 'Alice'))
solver.add(Implies(house_mothers[2] == 'Aniya', house_names[2] == 'Alice'))
solver.add(Implies(house_mothers[3] == 'Aniya', house_names[3] == 'Alice'))

# 13. Arnold is the person who loves the bouquet of lilies.
solver.add(Implies(house_names[0] == 'Arnold', house_flowers[0] == 'lilies'))
solver.add(Implies(house_names[1] == 'Arnold', house_flowers[1] == 'lilies'))
solver.add(Implies(house_names[2] == 'Arnold', house_flowers[2] == 'lilies'))
solver.add(Implies(house_names[3] == 'Arnold', house_flowers[3] == 'lilies'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in range(4):
        house_solution = [
            str(h + 1),
            model[house_names[h]].as_string(),
            model[house_flowers[h]].as_string(),
            model[house_heights[h]].as_string(),
            model[house_mothers[h]].as_string(),
            model[house_occupations[h]].as_string(),
            model[house_sports[h]].as_string()
        ]
        solution.append(house_solution)
    
    # Output the solution in JSON format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],' +
          f'"rows": {solution}' +
          '}'
          '}')
else:
    print("No solution found")