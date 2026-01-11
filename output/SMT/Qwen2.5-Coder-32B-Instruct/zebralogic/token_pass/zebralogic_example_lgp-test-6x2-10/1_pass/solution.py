from z3 import *

# Define the solver
solver = Solver()

# Define variables
names = [Int(f'name_{i}') for i in range(6)]
music_genres = [Int(f'music_genre_{i}') for i in range(6)]

# Define the domains for names and music genres
people = ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob']
music = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']

# Map names and music genres to integers
name_map = {name: i for i, name in enumerate(people)}
music_map = {genre: i for i, genre in enumerate(music)}

# Add constraints for uniqueness
solver.add(Distinct(names))
solver.add(Distinct(music_genres))

# Add constraints based on clues
# Clue 3: Carol is in the sixth house.
solver.add(names[5] == name_map['Carol'])
solver.add(music_genres[5] == music_map['country'])

# Clue 9: The person who loves hip-hop music is in the third house.
solver.add(music_genres[2] == music_map['hip hop'])

# Clue 4: Eric and the person who loves hip-hop music are next to each other.
eric_house = Int('eric_house')
solver.add(Or(eric_house == 1, eric_house == 2))  # Eric can only be in house 1 or 2
solver.add(Implies(eric_house == 1, names[0] == name_map['Eric']))
solver.add(Implies(eric_house == 2, names[1] == name_map['Eric']))

# Clue 2: Eric is somewhere to the left of the person who loves hip-hop music.
solver.add(Or(eric_house == 1, eric_house == 2))

# Clue 1: Bob is directly left of the person who loves jazz music.
bob_house = Int('bob_house')
jazz_house = Int('jazz_house')
solver.add(Or(bob_house == 0, bob_house == 1, bob_house == 2, bob_house == 3, bob_house == 4))
solver.add(jazz_house == bob_house + 1)
solver.add(names[bob_house] == name_map['Bob'])
solver.add(music_genres[jazz_house] == music_map['jazz'])

# Clue 6: Arnold is not in the fifth house.
solver.add(names[4] != name_map['Arnold'])

# Clue 7: Arnold is somewhere to the right of the person who loves pop music.
# Clue 8: The person who loves pop music is Peter.
peter_house = Int('peter_house')
solver.add(Or(peter_house == 0, peter_house == 1, peter_house == 2, peter_house == 3, peter_house == 4))
solver.add(names[peter_house] == name_map['Peter'])
solver.add(music_genres[peter_house] == music_map['pop'])
solver.add(arnold_house = Int('arnold_house'))
solver.add(Or(arnold_house == 1, arnold_house == 2, arnold_house == 3, arnold_house == 4, arnold_house == 5))
solver.add(names[arnold_house] == name_map['Arnold'])
solver.add(arnold_house > peter_house)

# Clue 10: There is one house between Peter and Bob.
solver.add(Abs(peter_house - bob_house) == 2)

# Clue 11: The person who loves rock music is not in the fifth house.
solver.add(music_genres[4] != music_map['rock'])

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(6):
        name = people[model.evaluate(names[i]).as_long()]
        genre = music[model.evaluate(music_genres[i]).as_long()]
        solution.append([str(i + 1), name, genre])
    
    print({
        "solution": {
            "header": ["House", "Name", "MusicGenre"],
            "rows": solution
        }
    })
else:
    print("No solution found")