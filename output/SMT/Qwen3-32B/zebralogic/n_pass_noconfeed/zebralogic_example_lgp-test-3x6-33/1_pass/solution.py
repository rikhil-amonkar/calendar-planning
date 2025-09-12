from z3 import *
import json

# Define EnumSorts for each attribute category
Names, (Arnold, Eric, Peter) = EnumSort('Names', ['Arnold', 'Eric', 'Peter'])
Flowers, (carnations, lilies, daffodils) = EnumSort('Flowers', ['carnations', 'lilies', 'daffodils'])
HairColors, (black, brown, blonde) = EnumSort('HairColors', ['black', 'brown', 'blonde'])
Sports, (soccer, basketball, tennis) = EnumSort('Sports', ['soccer', 'basketball', 'tennis'])
Styles, (colonial, ranch, victorian) = EnumSort('Styles', ['colonial', 'ranch', 'victorian'])
Pets, (fish, dog, cat) = EnumSort('Pets', ['fish', 'dog', 'cat'])

# Create variables for each house (0, 1, 2) and each attribute
name = [Const(f'name_{i}', Names) for i in range(3)]
flower = [Const(f'flower_{i}', Flowers) for i in range(3)]
hair_color = [Const(f'hair_color_{i}', HairColors) for i in range(3)]
sport = [Const(f'sport_{i}', Sports) for i in range(3)]
style = [Const(f'style_{i}', Styles) for i in range(3)]
pet = [Const(f'pet_{i}', Pets) for i in range(3)]

s = Solver()

# Add distinct constraints for each category
s.add(Distinct(name))
s.add(Distinct(flower))
s.add(Distinct(hair_color))
s.add(Distinct(sport))
s.add(Distinct(style))
s.add(Distinct(pet))

# Add puzzle constraints
# Clue 1: The person who has a cat loves soccer (house 3 has both)
s.add(pet[2] == cat, sport[2] == soccer)

# Clue 2: House 2 has blonde hair
s.add(hair_color[1] == blonde)

# Clue 3: Daffodils lover has blonde hair (house 2 has daffodils)
s.add(flower[1] == daffodils)

# Clue 4: Peter loves basketball
for i in range(3):
    s.add(Implies(name[i] == Peter, sport[i] == basketball))

# Clue 5: Arnold is directly left of ranch-style home
s.add(Or(
    And(name[0] == Arnold, style[1] == ranch),
    And(name[1] == Arnold, style[2] == ranch)
))

# Clue 6: Dog owner loves basketball
s.add(Or(
    And(pet[0] == dog, sport[0] == basketball),
    And(pet[1] == dog, sport[1] == basketball),
    And(pet[2] == dog, sport[2] == basketball)
))

# Clue 7: Carnations lover is directly left of blonde hair (house 1 has carnations)
s.add(flower[0] == carnations)

# Clue 8: Soccer lover is in house 3
s.add(sport[2] == soccer)

# Clue 9: Arnold is left of black hair
s.add(Or(
    And(name[0] == Arnold, Or(hair_color[1] == black, hair_color[2] == black)),
    And(name[1] == Arnold, hair_color[2] == black)
))

# Clue 10: Colonial-style house is in house 3
s.add(style[2] == colonial)

# Check for solution
if s.check() == sat:
    model = s.model()
    solution_data = {
        "solution": {
            "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
            "rows": []
        }
    }
    for i in range(3):
        house_num = str(i + 1)
        name_val = model.eval(name[i]).decl().name()
        flower_val = model.eval(flower[i]).decl().name()
        hair_color_val = model.eval(hair_color[i]).decl().name()
        sport_val = model.eval(sport[i]).decl().name()
        style_val = model.eval(style[i]).decl().name()
        pet_val = model.eval(pet[i]).decl().name()
        solution_data["solution"]["rows"].append([
            house_num, name_val, flower_val, hair_color_val, sport_val, style_val, pet_val
        ])
    print(json.dumps(solution_data, indent=2))
else:
    print("No solution found.")