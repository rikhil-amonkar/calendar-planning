from z3 import *

solver = Solver()

# Create variables for each attribute per house (0-5 indexes for houses 1-6)
Name = [Int(f'Name_{i}') for i in range(6)]
Cigar = [Int(f'Cigar_{i}') for i in range(6)]
Music = [Int(f'Music_{i}') for i in range(6)]
Drink = [Int(f'Drink_{i}') for i in range(6)]
Mother = [Int(f'Mother_{i}') for i in range(6)]
Food = [Int(f'Food_{i}') for i in range(6)]

# Add domain constraints (each attribute is 0-5, all distinct)
for attr in [Name, Cigar, Music, Drink, Mother, Food]:
    for i in range(6):
        solver.add(And(attr[i] >= 0, attr[i] < 6))
    solver.add(Distinct(attr))

# Add clues
# Clue 1: Carol (5) directly left of grilled cheese (5)
solver.add(Or([And(Name[h] == 5, Food[h+1] == 5) for h in range(5)]))

# Clue 2: Eric (2) not in house 2 (index 1)
solver.add(Name[1] != 2)

# Clue 3: Holly's mother (3) is to the right of Carol
carol_pos = Sum([If(Name[i] == 5, i, 0) for i in range(6)])
holly_pos = Sum([If(Mother[i] == 3, i, 0) for i in range(6)])
solver.add(carol_pos < holly_pos)

# Clue 4: grilled cheese (5) to the right of rock (5)
gc_pos = Sum([If(Food[i] ==5, i, 0) for i in range(6)])
rock_pos = Sum([If(Music[i] ==5, i, 0) for i in range(6)])
solver.add(rock_pos < gc_pos)

# Clue 5: Eric (2) directly left of Carol (5)
solver.add(Or([And(Name[h] == 2, Name[h+1] ==5) for h in range(5)]))

# Clue 6: pop (3) not in third house (index 2)
solver.add(Music[2] != 3)

# Clue 7: Eric's music is country (2)
for i in range(6):
    solver.add(Implies(Name[i] == 2, Music[i] == 2))

# Clue 8: classical (4) in sixth house (index 5)
solver.add(Music[5] == 4)

# Clue 9: Bob (3) drinks coffee (5)
for i in range(6):
    solver.add(Implies(Name[i] == 3, Drink[i] == 5))

# Clue 10: Peter (1) smokes blends (5)
for i in range(6):
    solver.add(Implies(Name[i] == 1, Cigar[i] == 5))

# Clue 11: Stew (4) not in fifth house (index 4)
solver.add(Food[4] != 4)

# Clue 12: root beer (4) directly left of Janelle (Mother 2)
solver.add(Or([And(Drink[h] ==4, Mother[h+1] ==2) for h in range(5)]))

# Clue 13: Sarah (4) and Yellow Monster (1) with 2 houses between
sarah_pos = Sum([If(Mother[i] ==4, i, 0) for i in range(6)])
yellow_pos = Sum([If(Cigar[i] ==1, i, 0) for i in range(6)])
solver.add(Abs(sarah_pos - yellow_pos) == 3)

# Clue 14: Eric (2) drinks tea (3)
for i in range(6):
    solver.add(Implies(Name[i] == 2, Drink[i] == 3))

# Clue 15: Pall Mall (0) to the right of stir fry (3)
stir_pos = Sum([If(Food[i] ==3, i, 0) for i in range(6)])
pall_pos = Sum([If(Cigar[i] ==0, i, 0) for i in range(6)])
solver.add(stir_pos < pall_pos)

# Clue 16: Bob (3) eats soup (0)
for i in range(6):
    solver.add(Implies(Name[i] == 3, Food[i] == 0))

# Clue 17: hip hop (0) directly left of Kailyn (Mother 0)
solver.add(Or([And(Music[h] ==0, Mother[h+1] ==0) for h in range(5)]))

# Clue 18: Arnold (4) to the right of Kailyn (Mother 0)
kailyn_pos = Sum([If(Mother[i] ==0, i, 0) for i in range(6)])
arnold_pos = Sum([If(Name[i] ==4, i, 0) for i in range(6)])
solver.add(kailyn_pos < arnold_pos)

# Clue 19: water (0) directly left of Blue Master (3)
solver.add(Or([And(Drink[h] ==0, Cigar[h+1] ==3) for h in range(5)]))

# Clue 20: spaghetti (2) left of Peter (1)
spaghetti_pos = Sum([If(Food[i] ==2, i, 0) for i in range(6)])
peter_pos = Sum([If(Name[i] ==1, i, 0) for i in range(6)])
solver.add(spaghetti_pos < peter_pos)

# Clue 21: Sarah (4) directly left of jazz (1)
solver.add(Or([And(Mother[h] ==4, Music[h+1] ==1) for h in range(5)]))

# Clue 22: hip hop (0) directly left of root beer (4)
solver.add(Or([And(Music[h] ==0, Drink[h+1] ==4) for h in range(5)]))

# Clue 23: water (0) drinker has stew (4)
for i in range(6):
    solver.add(Implies(Drink[i] ==0, Food[i] ==4))

# Clue 24: Dunhill (2) not in second house (index 1)
solver.add(Cigar[1] != 2)

# Clue 25: milk (1) drinker has mother Janelle (2)
for i in range(6):
    solver.add(Implies(Drink[i] ==1, Mother[i] ==2))

# Clue 26: Eric (2) has mother Aniya (5)
for i in range(6):
    solver.add(Implies(Name[i] ==2, Mother[i] ==5))

# Now check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Prepare the solution
    name_list = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
    cigar_list = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
    music_list = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
    drink_list = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
    mother_list = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
    food_list = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]
    
    rows = []
    for h in range(6):
        name_val = model.eval(Name[h]).as_long()
        cigar_val = model.eval(Cigar[h]).as_long()
        music_val = model.eval(Music[h]).as_long()
        drink_val = model.eval(Drink[h]).as_long()
        mother_val = model.eval(Mother[h]).as_long()
        food_val = model.eval(Food[h]).as_long()
        rows.append([
            str(h+1),
            name_list[name_val],
            cigar_list[cigar_val],
            music_list[music_val],
            drink_list[drink_val],
            mother_list[mother_val],
            food_list[food_val]
        ])
    # Now format as JSON
    import json
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
            "rows": rows
        }
    }
    print(json.dumps(solution_dict, indent=2))
else:
    print("No solution found.")