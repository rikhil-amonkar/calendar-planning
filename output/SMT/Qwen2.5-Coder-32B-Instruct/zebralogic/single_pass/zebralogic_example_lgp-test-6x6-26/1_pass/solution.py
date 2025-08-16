from z3 import *

# Define the variables
houses = range(1, 7)
names = ['Peter', 'Carol', 'Eric', 'Alice', 'Bob', 'Arnold']
phone_models = ['huawei p50', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'oneplus 9']
cigars = ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster']
flowers = ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris']
colors = ['yellow', 'red', 'green', 'blue', 'white', 'purple']
favorite_sports = ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']

# Create the solver
solver = Solver()

# Create dictionaries to map variables to their respective domains
name_vars = {house: Int(f'name_{house}') for house in houses}
phone_model_vars = {house: Int(f'phone_model_{house}') for house in houses}
cigar_vars = {house: Int(f'cigar_{house}') for house in houses}
flower_vars = {house: Int(f'flower_{house}') for house in houses}
color_vars = {house: Int(f'color_{house}') for house in houses}
favorite_sport_vars = {house: Int(f'favorite_sport_{house}') for house in houses}

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([phone_model_vars[house] for house in houses]))
solver.add(Distinct([cigar_vars[house] for house in houses]))
solver.add(Distinct([flower_vars[house] for house in houses]))
solver.add(Distinct([color_vars[house] for house in houses]))
solver.add(Distinct([favorite_sport_vars[house] for house in houses]))

# Map values to integers
value_to_int = {value: i for i, value in enumerate(names + phone_models + cigars + flowers + colors + favorite_sports)}

# Add clues as constraints
# Clue 1
solver.add(phone_model_vars[2] == value_to_int['oneplus 9'])

# Clue 2
solver.add(phone_model_vars[h] < phone_model_vars[k] for h in range(1, 6) for k in range(h+1, 7) if phone_models[value_to_int.index(phone_model_vars[h].as_long())] == 'xiaomi mi 11' and phone_models[value_to_int.index(phone_model_vars[k].as_long())] == 'huawei p50')

# Clue 3
solver.add(flower_vars[h] == value_to_int['carnations'] for h in houses if name_vars[h] == value_to_int['Carol'])

# Clue 4
solver.add(color_vars[h] == value_to_int['purple'] for h in houses if cigar_vars[h+1] == value_to_int['pall mall'])

# Clue 5
solver.add(cigar_vars[h] == value_to_int['blue master'] for h in houses if color_vars[h] == value_to_int['green'])

# Clue 6
solver.add(Or(And(color_vars[h] == value_to_int['yellow'], color_vars[h+1] == value_to_int['blue']), And(color_vars[h] == value_to_int['blue'], color_vars[h-1] == value_to_int['yellow'])) for h in range(2, 6))

# Clue 7
solver.add(Eric_house > Samsung_house for Eric_house in houses for Samsung_house in houses if name_vars[Eric_house] == value_to_int['Eric'] and phone_model_vars[Samsung_house] == value_to_int['samsung galaxy s21'])

# Clue 8
solver.add(Abs(Carol_house - Daffodils_house) == 2 for Carol_house in houses for Daffodils_house in houses if flower_vars[Carol_house] == value_to_int['carnations'] and flower_vars[Daffodils_house] == value_to_int['daffodils'])

# Clue 9
solver.add(cigar_vars[h] == value_to_int['prince'] for h in houses if favorite_sport_vars[h] == value_to_int['basketball'])

# Clue 10
solver.add(cigar_vars[h] == value_to_int['dunhill'] for h in houses if favorite_sport_vars[h] == value_to_int['volleyball'])

# Clue 11
solver.add(phone_model_vars[h] == value_to_int['google pixel 6'] for h in houses if favorite_sport_vars[h] == value_to_int['swimming'])

# Clue 12
solver.add(phone_model_vars[h] == value_to_int['huawei p50'] for h in houses if color_vars[h+1] == value_to_int['white'])

# Clue 13
solver.add(Or(phone_model_vars[h] == value_to_int['oneplus 9'] and flower_vars[h+1] == value_to_int['roses'], phone_model_vars[h+1] == value_to_int['oneplus 9'] and flower_vars[h] == value_to_int['roses']) for h in range(1, 6))

# Clue 14
solver.add(Iris_house < Eric_house for Iris_house in houses for Eric_house in houses if flower_vars[Iris_house] == value_to_int['iris'] and name_vars[Eric_house] == value_to_int['Eric'])

# Clue 15
solver.add(cigar_vars[h] == value_to_int['dunhill'] for h in houses if name_vars[h] == value_to_int['Peter'])

# Clue 16
solver.add(color_vars[h] == value_to_int['blue'] for h in houses if name_vars[h] == value_to_int['Peter'])

# Clue 17
solver.add(flower_vars[h] == value_to_int['tulips'] for h in houses if name_vars[h] == value_to_int['Bob'])

# Clue 18
solver.add(name_vars[1] == value_to_int['Alice'])

# Clue 19
solver.add(favorite_sport_vars[h] == value_to_int['baseball'] for h in houses if cigar_vars[h+1] == value_to_int['blue master'])

# Clue 20
solver.add(phone_model_vars[h] > Blends_house for h in range(1, 7) for Blends_house in houses if phone_model_vars[h] == value_to_int['google pixel 6'] and cigar_vars[Blends_house] == value_to_int['blends'])

# Clue 21
solver.add(favorite_sport_vars[h] == value_to_int['soccer'] for h in houses if name_vars[h] == value_to_int['Carol'])

# Clue 22
solver.add(Carnations_house < Blends_house for Carnations_house in houses for Blends_house in houses if flower_vars[Carnations_house] == value_to_int['carnations'] and cigar_vars[Blends_house] == value_to_int['blends'])

# Clue 23
solver.add(cigar_vars[h] == value_to_int['blends'] for h in houses if name_vars[h] == value_to_int['Eric'])

# Clue 24
solver.add(favorite_sport_vars[h] == value_to_int['volleyball'] for h in houses if phone_model_vars[h] == value_to_int['iphone 13'])

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        phone_model = phone_models[model.evaluate(phone_model_vars[house]).as_long()]
        cigar = cigars[model.evaluate(cigar_vars[house]).as_long()]
        flower = flowers[model.evaluate(flower_vars[house]).as_long()]
        color = colors[model.evaluate(color_vars[house]).as_long()]
        favorite_sport = favorite_sports[model.evaluate(favorite_sport_vars[house]).as_long()]
        solution.append([str(house), name, phone_model, cigar, flower, color, favorite_sport])
    
    print({
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
            "rows": solution
        }
    })
else:
    print("No solution found")