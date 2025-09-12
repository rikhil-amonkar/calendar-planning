from z3 import *
import json

# Define the possible options
nationalities = ['german', 'swede', 'norwegian', 'brit', 'dane']
names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
smoothies = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
animals = ['horse', 'dog', 'bird', 'fish', 'cat']

# Precompute indexes
swede_idx = nationalities.index('swede')
dane_idx = nationalities.index('dane')
norwegian_idx = nationalities.index('norwegian')
brit_idx = nationalities.index('brit')

eric_idx = names.index('Eric')
bob_idx = names.index('Bob')
alice_idx = names.index('Alice')
peter_idx = names.index('Peter')

lime_idx = smoothies.index('lime')
desert_idx = smoothies.index('desert')
watermelon_idx = smoothies.index('watermelon')
cherry_idx = smoothies.index('cherry')

horse_idx = animals.index('horse')
dog_idx = animals.index('dog')
bird_idx = animals.index('bird')
cat_idx = animals.index('cat')

# Create Z3 variables for each house's attributes
Nat = [ Int('Nat_%i' % (i+1)) for i in range(5) ]
Name = [ Int('Name_%i' % (i+1)) for i in range(5) ]
Smoothie = [ Int('Smoothie_%i' % (i+1)) for i in range(5) ]
Animal = [ Int('Animal_%i' % (i+1)) for i in range(5) ]

solver = Solver()

# Add constraints for each attribute to be between 0-4 and distinct
for var in Nat + Name + Smoothie + Animal:
    solver.add(And(0 <= var, var <= 4))

solver.add(Distinct(Nat))
solver.add(Distinct(Name))
solver.add(Distinct(Smoothie))
solver.add(Distinct(Animal))

# Clue 1: Swedish person is directly left of the dog owner
clue1 = Or([And(Nat[i] == swede_idx, Animal[i+1] == dog_idx) for i in range(4)])
solver.add(clue1)

# Clue 2: Two houses between dog owner and British person
D = Int('D')
B = Int('B')
solver.add(D >= 1, D <= 5)
solver.add(B >= 1, B <= 5)
solver.add(Animal[D-1] == dog_idx)
solver.add(Nat[B-1] == brit_idx)
solver.add(Or(D - B == 3, B - D == 3))

# Clue 3: Dane keeps horses
for h in range(5):
    solver.add(Implies(Nat[h] == dane_idx, Animal[h] == horse_idx))

# Clue 4: Bird keeper is somewhere to the right of cat lover
Y = Int('Y')
Z = Int('Z')
solver.add(Y >= 1, Y <= 5)
solver.add(Z >= 1, Z <= 5)
solver.add(Animal[Y-1] == bird_idx)
solver.add(Animal[Z-1] == cat_idx)
solver.add(Y > Z)

# Clue 5: Dog owner is directly left of Lime smoothie
solver.add(Smoothie[D] == lime_idx)

# Clue 6: Eric is the cat lover
solver.add(Name[Z-1] == eric_idx)

# Clue 7: Bob is the bird keeper
solver.add(Name[Y-1] == bob_idx)

# Clue 8: Cherry smoothie lover is directly left of Peter
C = Int('C')
solver.add(C >= 1, C <= 4)
solver.add(Smoothie[C-1] == cherry_idx)
solver.add(Name[C] == peter_idx)

# Clue 9: Bird keeper is Watermelon smoothie lover
solver.add(Smoothie[Y-1] == watermelon_idx)

# Clue 10: Desert smoothie lover is the dog owner
for h in range(5):
    solver.add(Implies(Smoothie[h] == desert_idx, Animal[h] == dog_idx))
clue10b = Or([And(Smoothie[i] == desert_idx, Animal[i] == dog_idx) for i in range(5)])
solver.add(clue10b)

# Clue 11: The person who keeps horses is in the third house
solver.add(Animal[2] == horse_idx)

# Clue 12: The Norwegian is Alice
for h in range(5):
    solver.add(Implies(Nat[h] == norwegian_idx, Name[h] == alice_idx))

if solver.check() == sat:
    model = solver.model()
    rows = []
    for i in range(5):
        house_num = i + 1
        nat_val = model[Nat[i]].as_long()
        name_val = model[Name[i]].as_long()
        smoothie_val = model[Smoothie[i]].as_long()
        animal_val = model[Animal[i]].as_long()
        nationality = nationalities[nat_val]
        name = names[name_val]
        smoothie = smoothies[smoothie_val]
        animal = animals[animal_val]
        rows.append([str(house_num), name, smoothie, animal, nationality])
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")