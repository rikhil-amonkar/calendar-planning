import json
from z3 import *

# Define EnumSorts
Name, (Peter, Arnold, Eric) = EnumSort('Name', ['Peter', 'Arnold', 'Eric'])
CarModel, (toyota_camry, ford_f150, tesla_model_3) = EnumSort('CarModel', ['toyota_camry', 'ford_f150', 'tesla_model_3'])
HouseStyle, (ranch, colonial, victorian) = EnumSort('HouseStyle', ['ranch', 'colonial', 'victorian'])
Pet, (cat, dog, fish) = EnumSort('Pet', ['cat', 'dog', 'fish'])
Occupation, (engineer, doctor, teacher) = EnumSort('Occupation', ['engineer', 'doctor', 'teacher'])
Vacation, (city, mountain, beach) = EnumSort('Vacation', ['city', 'mountain', 'beach'])

# Create variables for each house (0, 1, 2)
names = [Const(f'name_{i}', Name) for i in range(3)]
car_models = [Const(f'car_model_{i}', CarModel) for i in range(3)]
house_styles = [Const(f'house_style_{i}', HouseStyle) for i in range(3)]
pets = [Const(f'pet_{i}', Pet) for i in range(3)]
occupations = [Const(f'occupation_{i}', Occupation) for i in range(3)]
vacations = [Const(f'vacation_{i}', Vacation) for i in range(3)]

s = Solver()

# Add distinct constraints for each attribute
s.add(Distinct(names))
s.add(Distinct(car_models))
s.add(Distinct(house_styles))
s.add(Distinct(pets))
s.add(Distinct(occupations))
s.add(Distinct(vacations))

# Add constraints based on clues
# Clue 1: Fish in first house (index 0)
s.add(pets[0] == fish)

# Clue 2: Toyota Camry in second house (index 1)
s.add(car_models[1] == toyota_camry)

# Clue 3: Mountain not in second house (index 1)
s.add(vacations[1] != mountain)

# Clue 4: City not in second house (index 1)
s.add(vacations[1] != city)

# Clue 5: Ranch is left of Peter
s.add(Or(
    And(house_styles[0] == ranch, Or(names[1] == Peter, names[2] == Peter)),
    And(house_styles[1] == ranch, names[2] == Peter)
))

# Clue 6: Toyota Camry directly left of colonial house (so house_style[2] == colonial)
s.add(house_styles[2] == colonial)

# Clue 7: Arnold has cat
for i in range(3):
    s.add(Implies(names[i] == Arnold, pets[i] == cat))

# Clue 8: Eric left of mountain
s.add(Or(
    And(names[0] == Eric, Or(vacations[1] == mountain, vacations[2] == mountain)),
    And(names[1] == Eric, vacations[2] == mountain)
))

# Clue 9: Engineer not in third house (index 2)
s.add(occupations[2] != engineer)

# Clue 10: Tesla left of teacher
s.add(Or(
    And(car_models[0] == tesla_model_3, Or(occupations[1] == teacher, occupations[2] == teacher)),
    And(car_models[1] == tesla_model_3, occupations[2] == teacher)
))

# Clue 11: Dog owner is engineer
for i in range(3):
    s.add(Implies(pets[i] == dog, occupations[i] == engineer))

if s.check() == sat:
    model = s.model()
    rows = []
    for i in range(3):
        house_num = i + 1
        name = model.evaluate(names[i]).decl().name()
        car_model = model.evaluate(car_models[i]).decl().name().replace('_', ' ')
        house_style = model.evaluate(house_styles[i]).decl().name().replace('_', ' ')
        pet = model.evaluate(pets[i]).decl().name()
        occupation = model.evaluate(occupations[i]).decl().name()
        vacation = model.evaluate(vacations[i]).decl().name()
        rows.append([str(house_num), name, car_model, house_style, pet, occupation, vacation])
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")