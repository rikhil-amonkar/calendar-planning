import json
from z3 import *

# Define EnumSorts
Names, (Alice, Eric, Bob, Peter, Arnold) = EnumSort('Names', ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold'])
Birthdays, (mar, april, sept, feb, jan) = EnumSort('Birthdays', ['mar', 'april', 'sept', 'feb', 'jan'])
Mothers, (Holly, Janelle, Kailyn, Penny, Aniya) = EnumSort('Mothers', ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya'])
Occupations, (engineer, doctor, lawyer, artist, teacher) = EnumSort('Occupations', ['engineer', 'doctor', 'lawyer', 'artist', 'teacher'])
HairColors, (red, blonde, black, gray, brown) = EnumSort('HairColors', ['red', 'blonde', 'black', 'gray', 'brown'])

# Create functions for each attribute
name_func = Function('name', IntSort(), Names)
birthday_func = Function('birthday', IntSort(), Birthdays)
mother_func = Function('mother', IntSort(), Mothers)
occupation_func = Function('occupation', IntSort(), Occupations)
haircolor_func = Function('haircolor', IntSort(), HairColors)

s = Solver()

# Add uniqueness constraints for each attribute
for i in range(1, 6):
    for j in range(i + 1, 6):
        s.add(name_func(i) != name_func(j))
        s.add(birthday_func(i) != birthday_func(j))
        s.add(mother_func(i) != mother_func(j))
        s.add(occupation_func(i) != occupation_func(j))
        s.add(haircolor_func(i) != haircolor_func(j))

# Add clues
# Clue 1: birthday is mar in house 5
s.add(birthday_func(5) == mar)

# Clue 2: birthday is feb in house 1
s.add(birthday_func(1) == feb)

# Clue 3: doctor is Eric
for h in range(1, 6):
    s.add(Implies(occupation_func(h) == doctor, name_func(h) == Eric))

# Clue 4: mother is Janelle in house 3
s.add(mother_func(3) == Janelle)

# Clue 5: artist has brown hair
for h in range(1, 6):
    s.add(Implies(occupation_func(h) == artist, haircolor_func(h) == brown))

# Clue 6: artist is in house 4
s.add(occupation_func(4) == artist)

# Clue 7: Penny is left of black hair
clue7 = Or([And(mother_func(i) == Penny, haircolor_func(j) == black) for i in range(1, 6) for j in range(i + 1, 6)])
s.add(clue7)

# Clue 8: Peter has black hair
for h in range(1, 6):
    s.add(Implies(name_func(h) == Peter, haircolor_func(h) == black))

# Clue 9: gray hair is teacher
for h in range(1, 6):
    s.add(Implies(haircolor_func(h) == gray, occupation_func(h) == teacher))

# Clue 10: Alice's mother is Kailyn
for h in range(1, 6):
    s.add(Implies(name_func(h) == Alice, mother_func(h) == Kailyn))

# Clue 11: Arnold is right of sept birthday
for h1 in range(1, 6):
    for h2 in range(1, 6):
        s.add(Implies(And(birthday_func(h1) == sept, name_func(h2) == Arnold), h2 > h1))

# Clue 12: brown hair has jan birthday
for h in range(1, 6):
    s.add(Implies(haircolor_func(h) == brown, birthday_func(h) == jan))

# Clue 13: Arnold has blonde hair
for h in range(1, 6):
    s.add(Implies(name_func(h) == Arnold, haircolor_func(h) == blonde))

# Clue 14: Holly's mother has black hair
for h in range(1, 6):
    s.add(Implies(mother_func(h) == Holly, haircolor_func(h) == black))

# Clue 15: Peter is lawyer
for h in range(1, 6):
    s.add(Implies(name_func(h) == Peter, occupation_func(h) == lawyer))

# Clue 16: sept birthday is left of Kailyn mother
for h_sept in range(1, 6):
    for h_kailyn in range(1, 6):
        s.add(Implies(And(birthday_func(h_sept) == sept, mother_func(h_kailyn) == Kailyn), h_sept < h_kailyn))

# Clue 17: Alice has gray hair
for h in range(1, 6):
    s.add(Implies(name_func(h) == Alice, haircolor_func(h) == gray))

# Check for solution
if s.check() == sat:
    model = s.model()
    rows = []
    for h in range(1, 6):
        name_val = model.eval(name_func(h)).decl().name()
        birthday_val = model.eval(birthday_func(h)).decl().name()
        mother_val = model.eval(mother_func(h)).decl().name()
        occupation_val = model.eval(occupation_func(h)).decl().name()
        haircolor_val = model.eval(haircolor_func(h)).decl().name()
        rows.append([str(h), name_val, birthday_val, mother_val, occupation_val, haircolor_val])
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")