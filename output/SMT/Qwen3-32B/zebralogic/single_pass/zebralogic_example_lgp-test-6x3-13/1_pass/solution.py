import json
from z3 import *

# Define EnumSorts
Name, name_consts = EnumSort('Name', ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric'])
Bob, Arnold, Carol, Alice, Peter, Eric = name_consts

BookGenre, bg_consts = EnumSort('BookGenre', ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction'])
romance, historical_fiction, biography, mystery, fantasy, science_fiction = bg_consts

Occupation, occ_consts = EnumSort('Occupation', ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer'])
artist, doctor, nurse, engineer, teacher, lawyer = occ_consts

# Create variables for each house (1-6, indexes 0-5)
name_vars = [Const(f'name_{i}', Name) for i in range(1, 7)]
bg_vars = [Const(f'bg_{i}', BookGenre) for i in range(1, 7)]
occ_vars = [Const(f'occ_{i}', Occupation) for i in range(1, 7)]

s = Solver()

# Add distinct constraints
s.add(Distinct(name_vars))
s.add(Distinct(bg_vars))
s.add(Distinct(occ_vars))

# Clue 1 and 4: Alice loves fantasy and is lawyer
for i in range(6):
    s.add(If(name_vars[i] == Alice, And(bg_vars[i] == fantasy, occ_vars[i] == lawyer), True))

# Clue 3: Carol loves mystery
for i in range(6):
    s.add(If(name_vars[i] == Carol, bg_vars[i] == mystery, True))

# Clue 12: Eric is in house 3 (index 2)
s.add(name_vars[2] == Eric)

# Clue 10: Doctor in house 1 (index 0)
s.add(occ_vars[0] == doctor)

# Clue 2: Carol and Bob are adjacent
for i in range(6):
    carol_here = name_vars[i] == Carol
    if i == 0:
        adjacent_bob = name_vars[i+1] == Bob
    elif i == 5:
        adjacent_bob = name_vars[i-1] == Bob
    else:
        adjacent_bob = Or(name_vars[i-1] == Bob, name_vars[i+1] == Bob)
    s.add(Implies(carol_here, adjacent_bob))

# Clue 5: Bob not in house 5 (index 4)
s.add(name_vars[4] != Bob)

# Clue 7: Nurse directly left of Alice
for i in range(5):  # i ranges 0-4, i+1 is 1-5
    alice_here = name_vars[i+1] == Alice
    nurse_prev = occ_vars[i] == nurse
    s.add(Implies(alice_here, nurse_prev))

# Clue 6: Arnold left of engineer
for i in range(6):
    for j in range(6):
        s.add(Implies(And(name_vars[i] == Arnold, occ_vars[j] == engineer), i < j))

# Clue 8: Biography → teacher
for i in range(6):
    s.add(Implies(bg_vars[i] == biography, occ_vars[i] == teacher))

# Clue 9: historical fiction left of teacher
for i in range(6):
    for j in range(6):
        s.add(Implies(And(bg_vars[i] == historical_fiction, occ_vars[j] == teacher), i < j))

# Clue 11: science fiction → artist
for i in range(6):
    s.add(Implies(bg_vars[i] == science_fiction, occ_vars[i] == artist))

# Clue 13: Carol not in house 5 (index 4)
s.add(name_vars[4] != Carol)

if s.check() == sat:
    model = s.model()
    solution = []
    for i in range(6):  # 0-5 for houses 1-6
        house_num = i + 1
        name = model[name_vars[i]].decl().name()
        book_genre = model[bg_vars[i]].decl().name()
        occupation = model[occ_vars[i]].decl().name()
        solution.append([str(house_num), name, book_genre, occupation])
    # Now, format into the required JSON structure
    json_output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": solution
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")