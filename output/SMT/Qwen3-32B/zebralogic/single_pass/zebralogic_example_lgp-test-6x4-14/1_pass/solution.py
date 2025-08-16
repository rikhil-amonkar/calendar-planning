from z3 import *
import json

# Define EnumSorts
Names, (Eric, Bob, Peter, Alice, Arnold, Carol) = EnumSort('Names', ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol'])
Cars, (ford_f150, honda_civic, toyota_camry, tesla_model_3, chevrolet_silverado, bmw_3_series) = EnumSort('Cars', ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series'])
Mothers, (Sarah, Penny, Holly, Aniya, Kailyn, Janelle) = EnumSort('Mothers', ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle'])
Hobbies, (photography, cooking, knitting, gardening, woodworking, painting) = EnumSort('Hobbies', ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting'])

# Create variables for each house (1-6)
name = [Const(f'name_{i}', Names) for i in range(1,7)]
car = [Const(f'car_{i}', Cars) for i in range(1,7)]
mother = [Const(f'mother_{i}', Mothers) for i in range(1,7)]
hobby = [Const(f'hobby_{i}', Hobbies) for i in range(1,7)]

solver = Solver()

# Add distinctness constraints
solver.add(Distinct(name))
solver.add(Distinct(car))
solver.add(Distinct(mother))
solver.add(Distinct(hobby))

# Clue 1: car[6] is toyota camry
solver.add(car[5] == toyota_camry)

# Clue 2: Carol's hobby is photography
for i in range(6):
    solver.add(Or(name[i] != Carol, hobby[i] == photography))

# Clue 3: chevrolet_silverado's mother is Aniya
for i in range(6):
    solver.add(Or(car[i] != chevrolet_silverado, mother[i] == Aniya))

# Clue 4: car[2] != chevrolet_silverado
solver.add(car[1] != chevrolet_silverado)

# Clue 5: ford_f150's mother is Sarah
for i in range(6):
    solver.add(Or(car[i] != ford_f150, mother[i] == Sarah))

# Clue 6: Bob's car is bmw_3_series
for i in range(6):
    solver.add(Or(name[i] != Bob, car[i] == bmw_3_series))

# Clue 7: mother[6] is Kailyn
solver.add(mother[5] == Kailyn)

# Clue 8: Eric is directly left of knitting
solver.add(Or([And(name[i] == Eric, hobby[i+1] == knitting) for i in range(5)]))

# Clue 9: mother Sarah is in house 4 (index 3)
for i in range(6):
    solver.add(Or(mother[i] != Sarah, i == 3))

# Clue 15: cooking is in house 2 or 6 (index 1 or 5)
solver.add(Or(hobby[1] == cooking, hobby[5] == cooking))

# Clue 10: Penny's mother is to the right of knitting
i_knitting = Int('i_knitting')
solver.add(Or([And(hobby[i] == knitting, i_knitting == i) for i in range(6)]))
j_penny = Int('j_penny')
solver.add(Or([And(mother[i] == Penny, j_penny == i) for i in range(6)]))
solver.add(j_penny > i_knitting)

# Clue 11: Aniya's mother is to the right of Honda Civic (Arnold's car)
i_arnold = Int('i_arnold')
solver.add(Or([And(name[i] == Arnold, car[i] == honda_civic, i_arnold == i) for i in range(6)]))
j_aniya = Int('j_aniya')
solver.add(Or([And(mother[i] == Aniya, j_aniya == i) for i in range(6)]))
solver.add(j_aniya > i_arnold)

# Clue 12: Alice is to the right of Ford F150 (house 4, index 3)
i_alice = Int('i_alice')
solver.add(Or([And(name[i] == Alice, i_alice == i) for i in range(6)]))
solver.add(i_alice > 3)

# Clue 13: Eric's hobby is gardening
for i in range(6):
    solver.add(Or(name[i] != Eric, hobby[i] == gardening))

# Clue 17: Holly's mother is directly left of knitting
i_holly = Int('i_holly')
solver.add(Or([And(mother[i] == Holly, i_holly == i) for i in range(6)]))
solver.add(i_knitting == i_holly + 1)

# Clue 14: woodworking is left of knitting
i_woodworking = Int('i_woodworking')
solver.add(Or([And(hobby[i] == woodworking, i_woodworking == i) for i in range(6)]))
solver.add(i_woodworking < i_knitting)

# Clue 5 and 9: Ford F150 is in house 4 (index 3)
solver.add(car[3] == ford_f150)

if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(6):
        house_num = i + 1
        name_val = model[name[i]].decl().name()
        car_val = model[car[i]].decl().name()
        mother_val = model[mother[i]].decl().name()
        hobby_val = model[hobby[i]].decl().name()
        solution.append([str(house_num), name_val, car_val, mother_val, hobby_val])
    output = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")