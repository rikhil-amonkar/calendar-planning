from z3 import *
import json

# Define the possible values for each attribute
names_list = ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']
cigars_list = ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']
music_list = ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']
drinks_list = ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']
mothers_list = ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']
foods_list = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']

houses = 6

# Create Z3 variables for each attribute and house
name = [Int(f'name_{i}') for i in range(houses)]
cigar = [Int(f'cigar_{i}') for i in range(houses)]
music = [Int(f'music_{i}') for i in range(houses)]
drink = [Int(f'drink_{i}') for i in range(houses)]
mother = [Int(f'mother_{i}') for i in range(houses)]
food = [Int(f'food_{i}') for i in range(houses)]

solver = Solver()

# Add constraints for distinct values and valid range (0-5)
for attr in [name, cigar, music, drink, mother, food]:
    for i in range(houses):
        solver.add(And(0 <= attr[i], attr[i] < 6))
    solver.add(Distinct(attr))

# Add constraints based on the clues
# Clue 1: Carol is directly left of grilled cheese
solver.add(Or([And(name[i] == 5, food[i+1] == 5) for i in range(houses - 1)]))

# Clue 2: Eric is not in the second house
solver.add(name[1] != 2)

# Clue 3: Holly's mother is to the right of Carol
for i in range(houses):
    for j in range(houses):
        solver.add(Implies(And(name[i] == 5, mother[j] == 3), j > i))

# Clue 4: Grilled cheese is to the right of rock music
for g in range(houses):
    for r in range(houses):
        solver.add(Implies(And(food[g] == 5, music[r] == 5), g > r))

# Clue 5: Eric is directly left of Carol
solver.add(Or([And(name[i] == 2, name[i+1] == 5) for i in range(houses - 1)]))

# Clue 6: Pop music is not in the third house
solver.add(music[2] != 3)

# Clue 7: Eric's music is country
for i in range(houses):
    solver.add(Implies(name[i] == 2, music[i] == 2))

# Clue 8: Classical music is in the sixth house
solver.add(music[5] == 4)

# Clue 9: Coffee drinker is Bob
for i in range(houses):
    solver.add(Implies(drink[i] == 5, name[i] == 3))

# Clue 10: Peter smokes blends
for i in range(houses):
    solver.add(Implies(name[i] == 1, cigar[i] == 5))

# Clue 11: Stew is not in the fifth house
solver.add(food[4] != 4)

# Clue 12: Root beer lover is directly left of mother Janelle
solver.add(Or([And(drink[i] == 4, mother[i+1] == 2) for i in range(houses - 1)]))

# Clue 13: Two houses between Sarah and Yellow Monster
for s in range(houses):
    for y in range(houses):
        solver.add(Implies(And(mother[s] == 4, cigar[y] == 1), Or(s - y == 3, y - s == 3)))

# Clue 14: Eric is the tea drinker
for i in range(houses):
    solver.add(Implies(name[i] == 2, drink[i] == 3))

# Clue 15: Pall Mall is to the right of stir fry
for p in range(houses):
    for s in range(houses):
        solver.add(Implies(And(cigar[p] == 0, food[s] == 3), p > s))

# Clue 16: Soup is Bob's food
for i in range(houses):
    solver.add(Implies(name[i] == 3, food[i] == 0))

# Clue 17: Hip-hop music is directly left of mother Kailyn
solver.add(Or([And(music[i] == 0, mother[i+1] == 0) for i in range(houses - 1)]))

# Clue 18: Arnold is to the right of mother Kailyn
for a in range(houses):
    for k in range(houses):
        solver.add(Implies(And(name[a] == 4, mother[k] == 0), a > k))

# Clue 19: Water drinker is directly left of Blue Master smoker
solver.add(Or([And(drink[i] == 0, cigar[i+1] == 3) for i in range(houses - 1)]))

# Clue 20: Spaghetti is to the left of Peter
for s in range(houses):
    for p in range(houses):
        solver.add(Implies(And(food[s] == 2, name[p] == 1), s < p))

# Clue 21: Mother Sarah is directly left of jazz music
solver.add(Or([And(mother[i] == 4, music[i+1] == 1) for i in range(houses - 1)]))

# Clue 22: Hip-hop is directly left of root beer lover
solver.add(Or([And(music[i] == 0, drink[i+1] == 4) for i in range(houses - 1)]))

# Clue 23: Water drinker is the stew lover
for i in range(houses):
    solver.add(Implies(drink[i] == 0, food[i] == 4))
    solver.add(Implies(food[i] == 4, drink[i] == 0))

# Clue 24: Dunhill smoker not in second house
solver.add(cigar[1] != 2)

# Clue 25: Milk drinker is mother Janelle
for i in range(houses):
    solver.add(Implies(drink[i] == 1, mother[i] == 2))
    solver.add(Implies(mother[i] == 2, drink[i] == 1))

# Clue 26: Eric's mother is Aniya
for i in range(houses):
    solver.add(Implies(name[i] == 2, mother[i] == 5))

# Solve and output the solution
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(houses):
        n = model[name[i]].as_long()
        c = model[cigar[i]].as_long()
        m = model[music[i]].as_long()
        d = model[drink[i]].as_long()
        mo = model[mother[i]].as_long()
        f = model[food[i]].as_long()
        solution.append([str(i+1), names_list[n], cigars_list[c], music_list[m], drinks_list[d], mothers_list[mo], foods_list[f]])
    print(json.dumps({"solution": {"header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"], "rows": solution}}, indent=2))
else:
    print("No solution found.")