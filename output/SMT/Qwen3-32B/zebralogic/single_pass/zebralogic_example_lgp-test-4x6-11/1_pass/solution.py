from z3 import *
import json

s = Solver()

name = [Int(f'name_{i}') for i in range(4)]
hobby = [Int(f'hobby_{i}') for i in range(4)]
animal = [Int(f'animal_{i}') for i in range(4)]
book = [Int(f'book_{i}') for i in range(4)]
birthday = [Int(f'birthday_{i}') for i in range(4)]
music = [Int(f'music_{i}') for i in range(4)]

for category in [name, hobby, animal, book, birthday, music]:
    s.add(Distinct(category))
    for v in category:
        s.add(And(0 <= v, v <= 3))

# Clue 1: cooking (0) ↔ romance (2)
for i in range(4):
    s.add((hobby[i] == 0) == (book[i] == 2))

# Clue 2: birthday feb (3) ↔ music pop (0)
for i in range(4):
    s.add((birthday[i] == 3) == (music[i] == 0))

# Clue 3: Eric (2) not in house 2 (index 1)
s.add(name[1] != 2)

# Clue 4: book[3] != 2
s.add(book[3] != 2)

# Clue 5: birthday feb (3) ↔ animal fish (1)
for i in range(4):
    s.add((birthday[i] == 3) == (animal[i] == 1))

# Clue 6: Alice (1) to the right of fantasy (book 0)
for i in range(4):
    for j in range(4):
        s.add(Implies(And(book[i] == 0, name[j] == 1), j > i))

# Clue 7: animal horse (0) ↔ music rock (1)
for i in range(4):
    s.add((animal[i] == 0) == (music[i] == 1))

# Clue 8: hobby gardening (2) ↔ birthday april (0)
for i in range(4):
    s.add((hobby[i] == 2) == (birthday[i] == 0))

# Clue 9: music jazz (3) ↔ hobby cooking (0)
for i in range(4):
    s.add((music[i] == 3) == (hobby[i] == 0))

# Clue 10: music rock (1) ↔ book mystery (1)
for i in range(4):
    s.add((music[i] == 1) == (book[i] == 1))

# Clue 11: painting (1) directly left of romance (book 2)
s.add(Or(
    And(hobby[0] == 1, book[1] == 2),
    And(hobby[1] == 1, book[2] == 2),
    And(hobby[2] == 1, book[3] == 2)
))

# Clue 12: Peter (0) ↔ music pop (0)
for i in range(4):
    s.add((name[i] == 0) == (music[i] == 0))

# Clue 13: hobby gardening (2) ↔ Arnold (3)
for i in range(4):
    s.add((hobby[i] == 2) == (name[i] == 3))

# Clue 14: music rock (1) directly left of birthday jan (1)
s.add(Or(
    And(music[0] == 1, birthday[1] == 1),
    And(music[1] == 1, birthday[2] == 1),
    And(music[2] == 1, birthday[3] == 1)
))

# Clue 15: hobby[2] != 0
s.add(hobby[2] != 0)

# Clue 16: cat (2) to the right of horse (0)
for i in range(4):
    for j in range(4):
        s.add(Implies(And(animal[i] == 0, animal[j] == 2), j > i))

if s.check() == sat:
    model = s.model()
    name_values = ['Peter', 'Alice', 'Eric', 'Arnold']
    hobby_values = ['cooking', 'painting', 'gardening', 'photography']
    animal_values = ['horse', 'fish', 'cat', 'bird']
    book_values = ['fantasy', 'mystery', 'romance', 'science fiction']
    birthday_values = ['april', 'jan', 'sept', 'feb']
    music_values = ['pop', 'rock', 'classical', 'jazz']
    solution = []
    for i in range(4):
        house_num = i + 1
        n = model[name[i]].as_long()
        h = model[hobby[i]].as_long()
        a = model[animal[i]].as_long()
        b = model[book[i]].as_long()
        d = model[birthday[i]].as_long()
        m = model[music[i]].as_long()
        solution.append([
            str(house_num),
            name_values[n],
            hobby_values[h],
            animal_values[a],
            book_values[b],
            birthday_values[d],
            music_values[m]
        ])
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")