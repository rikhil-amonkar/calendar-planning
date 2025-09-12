import z3

# Initialize the solver
s = z3.Solver()

# Define variables for each house (0-5) and each attribute
names = [z3.Int('name_%d' % i) for i in range(6)]
pets = [z3.Int('pet_%d' % i) for i in range(6)]
styles = [z3.Int('style_%d' % i) for i in range(6)]
birthdays = [z3.Int('birthday_%d' % i) for i in range(6)]

# Add constraints for distinct and valid ranges
for var_list in [names, pets, styles, birthdays]:
    s.add(z3.Distinct(var_list))
    for var in var_list:
        s.add(z3.And(0 <= var, var < 6))

# Add fixed constraints
s.add(birthdays[1] == 2)  # Clue 3: May in house 2
s.add(styles[1] == 4)     # Clue 4: Colonial in house 2
s.add(names[2] == 2)      # Clue 5: Carol in house 3
s.add(names[5] == 3)      # Clue 8: Eric in house 6
s.add(styles[3] == 5)     # Clue 18: Craftsman in house 4
s.add(pets[3] == 1)       # Clue 19: Dog in house 4
s.add(birthdays[2] == 0)  # Clue 17: March in house 3
s.add(names[1] == 0)      # Clue 14: Peter in house 2
s.add(names[3] == 5)      # Clue 11: Arnold in house 4
s.add(styles[5] != 3)     # Clue 6: Mediterranean not in house 6
s.add(pets[1] != 4)       # Clue 13: Fish not in house 2

# Clue 2: Jan left of Sept
for i in range(6):
    for j in range(6):
        s.add(z3.Implies(z3.And(birthdays[i] == 4, birthdays[j] == 1), i < j))

# Clue 15: Jan directly left of April
i_jan_apr = z3.Int('i_jan_apr')
s.add(z3.And(i_jan_apr >= 0, i_jan_apr <= 4))
s.add(birthdays[i_jan_apr] == 4)
s.add(birthdays[i_jan_apr + 1] == 5)

# Clue 1: Hamster right of March (house 3, index 2)
for j in range(6):
    s.add(z3.Implies(pets[j] == 5, j > 2))

# Clue 7: Fish right of Bob
for i in range(6):
    for j in range(6):
        s.add(z3.Implies(z3.And(names[i] == 1, pets[j] == 4), j > i))

# Clue 12: Modern after Colonial (Colonial is at index 1)
for j in range(6):
    s.add(z3.Implies(styles[j] == 2, j > 1))

# Clue 9: Cat and Victorian
i_cat = z3.Int('i_cat')
i_victorian = z3.Int('i_victorian')
j_cat = z3.Int('j_cat')
j_victorian = z3.Int('j_victorian')
s.add(z3.And(i_cat >= 0, i_cat <= 5, i_victorian >= 0, i_victorian <= 5))
s.add(z3.ForAll(j_cat, z3.Implies(pets[j_cat] == 2, j_cat == i_cat)))
s.add(z3.ForAll(j_victorian, z3.Implies(styles[j_victorian] == 0, j_victorian == i_victorian)))
s.add(z3.Abs(i_cat - i_victorian) == 2)

# Clue 10: Victorian and Hamster
i_hamster = z3.Int('i_hamster')
j_hamster = z3.Int('j_hamster')
s.add(z3.And(i_hamster >= 0, i_hamster <= 5))
s.add(z3.ForAll(j_hamster, z3.Implies(pets[j_hamster] == 5, j_hamster == i_hamster)))
s.add(z3.Abs(i_victorian - i_hamster) == 3)

# Clue 16: Bird and Modern
i_bird = z3.Int('i_bird')
i_modern = z3.Int('i_modern')
j_bird = z3.Int('j_bird')
j_modern = z3.Int('j_modern')
s.add(z3.And(i_bird >= 0, i_bird <= 5, i_modern >= 0, i_modern <= 5))
s.add(z3.ForAll(j_bird, z3.Implies(pets[j_bird] == 0, j_bird == i_bird)))
s.add(z3.ForAll(j_modern, z3.Implies(styles[j_modern] == 2, j_modern == i_modern)))
s.add(z3.Abs(i_bird - i_modern) == 2)

if s.check() == z3.sat:
    model = s.model()
    names_list = ['Peter', 'Bob', 'Carol', 'Eric', 'Alice', 'Arnold']
    pets_list = ['bird', 'dog', 'cat', 'rabbit', 'fish', 'hamster']
    styles_list = ['victorian', 'ranch', 'modern', 'mediterranean', 'colonial', 'craftsman']
    birthdays_list = ['mar', 'sept', 'may', 'feb', 'jan', 'april']
    
    solution_rows = []
    for house_idx in range(6):
        house_num = house_idx + 1
        name_val = names_list[model[names[house_idx]].as_long()]
        pet_val = pets_list[model[pets[house_idx]].as_long()]
        style_val = styles_list[model[styles[house_idx]].as_long()]
        birthday_val = birthdays_list[model[birthdays[house_idx]].as_long()]
        solution_rows.append([str(house_num), name_val, pet_val, style_val, birthday_val])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": solution_rows
        }
    }
    
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")