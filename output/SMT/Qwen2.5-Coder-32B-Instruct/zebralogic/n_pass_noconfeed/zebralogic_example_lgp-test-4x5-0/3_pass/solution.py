from z3 import *

# Define the variables
names = ['Eric', 'Peter', 'Arnold', 'Alice']
smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
heights = ['tall', 'average', 'short', 'very short']
phone_models = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']

houses = [1, 2, 3, 4]

# Create the solver
solver = Solver()

# Create dictionaries to hold the variables
name_vars = {house: Int(f'name_{house}') for house in houses}
smoothie_vars = {house: Int(f'smoothie_{house}') for house in houses}
cigar_vars = {house: Int(f'cigar_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}
phone_model_vars = {house: Int(f'phone_model_{house}') for house in houses}

# Add domain constraints
for house in houses:
    solver.add(name_vars[house] >= 0)
    solver.add(name_vars[house] < len(names))
    solver.add(smoothie_vars[house] >= 0)
    solver.add(smoothie_vars[house] < len(smoothies))
    solver.add(cigar_vars[house] >= 0)
    solver.add(cigar_vars[house] < len(cigars))
    solver.add(height_vars[house] >= 0)
    solver.add(height_vars[house] < len(heights))
    solver.add(phone_model_vars[house] >= 0)
    solver.add(phone_model_vars[house] < len(phone_models))

# All values must be unique across houses
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([smoothie_vars[house] for house in houses]))
solver.add(Distinct([cigar_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))
solver.add(Distinct([phone_model_vars[house] for house in houses]))

# Clues
# 1. The Dragonfruit smoothie lover is Eric.
for house in houses:
    solver.add(Implies(smoothie_vars[house] == smoothies.index('dragonfruit'),
                       name_vars[house] == names.index('Eric')))

# 2. The Dunhill smoker is the person who likes Cherry smoothies.
for house in houses:
    solver.add(Implies(cigar_vars[house] == cigars.index('dunhill'),
                       smoothie_vars[house] == smoothies.index('cherry')))

# 3. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
for house in houses[:-1]:
    solver.add(Implies(phone_model_vars[house] == phone_models.index('samsung galaxy s21'),
                       phone_model_vars[house + 1] == phone_models.index('iphone 13')))

# 4. The Dunhill smoker is somewhere to the right of the person who is very short.
for h1 in range(2, 5):
    for h2 in range(1, h1):
        solver.add(Implies(cigar_vars[h1] == cigars.index('dunhill'),
                           height_vars[h2] == heights.index('very short')))

# 5. The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
for h1 in range(2, 5):
    for h2 in range(1, h1):
        solver.add(Implies(smoothie_vars[h1] == smoothies.index('watermelon'),
                           smoothie_vars[h2] == smoothies.index('desert')))

# 6. The Prince smoker is the person who uses a OnePlus 9.
for house in houses:
    solver.add(Implies(cigar_vars[house] == cigars.index('prince'),
                       phone_model_vars[house] == phone_models.index('oneplus 9')))

# 7. The person who is tall is in the third house.
solver.add(height_vars[3] == heights.index('tall'))

# 8. The person who is very short is the person who uses an iPhone 13.
for house in houses:
    solver.add(Implies(phone_model_vars[house] == phone_models.index('iphone 13'),
                       height_vars[house] == heights.index('very short')))

# 9. The person who smokes Blue Master is not in the first house.
solver.add(cigar_vars[1] != cigars.index('blue master'))

# 10. The Dunhill smoker is the person who is short.
for house in houses:
    solver.add(Implies(cigar_vars[house] == cigars.index('dunhill'),
                       height_vars[house] == heights.index('short')))

# 11. Peter is not in the third house.
solver.add(name_vars[3] != names.index('Peter'))

# 12. Arnold is the person who uses a Google Pixel 6.
for house in houses:
    solver.add(Implies(phone_model_vars[house] == phone_models.index('google pixel 6'),
                       name_vars[house] == names.index('Arnold')))

# 13. The Dragonfruit smoothie lover is the person partial to Pall Mall.
for house in houses:
    solver.add(Implies(smoothie_vars[house] == smoothies.index('dragonfruit'),
                       cigar_vars[house] == cigars.index('pall mall')))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        smoothie = smoothies[model[smoothie_vars[house]].as_long()]
        cigar = cigars[model[cigar_vars[house]].as_long()]
        height = heights[model[height_vars[house]].as_long()]
        phone_model = phone_models[model[phone_model_vars[house]].as_long()]
        solution.append([str(house), name, smoothie, cigar, height, phone_model])

    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": solution
        }
    }))
else:
    print("No solution found")