import z3
import json

name_list = ['Arnold', 'Eric', 'Peter']
flower_list = ['carnations', 'lilies', 'daffodils']
haircolor_list = ['black', 'brown', 'blonde']
sport_list = ['soccer', 'basketball', 'tennis']
housestyle_list = ['colonial', 'ranch', 'victorian']
pet_list = ['fish', 'dog', 'cat']

s = z3.Solver()

# Variables for each house (0,1,2)
names = [z3.Int('name_%d' % i) for i in range(3)]
flowers = [z3.Int('flower_%d' % i) for i in range(3)]
haircolors = [z3.Int('haircolor_%d' % i) for i in range(3)]
sports = [z3.Int('sport_%d' % i) for i in range(3)]
housestyles = [z3.Int('housestyle_%d' % i) for i in range(3)]
pets = [z3.Int('pet_%d' % i) for i in range(3)]

# All attributes must be distinct per category
for var_list in [names, flowers, haircolors, sports, housestyles, pets]:
    s.add(z3.Distinct(var_list))

# Each variable is between 0 and 2
for var_list in [names, flowers, haircolors, sports, housestyles, pets]:
    for var in var_list:
        s.add(z3.And(var >= 0, var <= 2))

# Clue 2: house 2 (index 1) has blonde (haircolor 2)
s.add(haircolors[1] == 2)

# Clue 3: flower[1] == 2 (daffodils)
s.add(flowers[1] == 2)

# Clue 7: flower[0] == 0 (carnations)
s.add(flowers[0] == 0)

# Clue 8: sports[2] == 0 (soccer)
s.add(sports[2] == 0)

# Clue 10: housestyles[2] == 0 (colonial)
s.add(housestyles[2] == 0)

# Clue 1: if pet[i] == 2 (cat) then sport[i] == 0 (soccer)
for i in range(3):
    s.add(z3.Implies(pets[i] == 2, sports[i] == 0))

# Also, since sports[2] is 0, pet[2] must be 2 (from clue 1)
s.add(pets[2] == 2)

# Clue 6: if pet[i] == 1 (dog) then sport[i] == 1 (basketball)
for i in range(3):
    s.add(z3.Implies(pets[i] == 1, sports[i] == 1))

# Clue 4 and 6: Peter (name == 2) has sport == 1 (basketball) and pet == 1 (dog)
for i in range(3):
    s.add(z3.Implies(names[i] == 2, z3.And(sports[i] == 1, pets[i] == 1)))

# Clue 5: if name[i] == 0 (Arnold), then i+1 <=2 and housestyles[i+1] == 1 (ranch)
for i in range(3):
    s.add(z3.Implies(names[i] == 0, z3.And(i+1 <= 2, housestyles[i+1] == 1)))

# Clue 9: if name[i] == 0 (Arnold), then there exists j > i with haircolor[j] == 0 (black)
for i in range(3):
    s.add(z3.Implies(names[i] == 0, z3.Or([haircolors[j] == 0 for j in range(i+1, 3)])))

if s.check() == z3.sat:
    model = s.model()
    # Now extract the values for each house
    houses = []
    for i in range(3):
        house_num = i + 1
        name_val = model[names[i]].as_long()
        flower_val = model[flowers[i]].as_long()
        haircolor_val = model[haircolors[i]].as_long()
        sport_val = model[sports[i]].as_long()
        housestyle_val = model[housestyles[i]].as_long()
        pet_val = model[pets[i]].as_long()
        houses.append([
            str(house_num),
            name_list[name_val],
            flower_list[flower_val],
            haircolor_list[haircolor_val],
            sport_list[sport_val],
            housestyle_list[housestyle_val],
            pet_list[pet_val]
        ])
    # Now, the solution is in houses, ordered by house_num 1,2,3
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
            "rows": houses
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution")