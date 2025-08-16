import json
from z3 import *

# Define EnumSorts for each attribute
Name, (Alice, Eric, Bob, Peter, Arnold) = EnumSort('Name', ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold'])
Birthday, (mar, april, sept, feb, jan) = EnumSort('Birthday', ['mar', 'april', 'sept', 'feb', 'jan'])
Mother, (Holly, Janelle, Kailyn, Penny, Aniya) = EnumSort('Mother', ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya'])
Occupation, (engineer, doctor, lawyer, artist, teacher) = EnumSort('Occupation', ['engineer', 'doctor', 'lawyer', 'artist', 'teacher'])
HairColor, (red, blonde, black, gray, brown) = EnumSort('HairColor', ['red', 'blonde', 'black', 'gray', 'brown'])

# Create variables for each house (0-based index for houses 1-5)
name = [Const(f'name_{i}', Name) for i in range(5)]
birthday = [Const(f'birthday_{i}', Birthday) for i in range(5)]
mother = [Const(f'mother_{i}', Mother) for i in range(5)]
occupation = [Const(f'occupation_{i}', Occupation) for i in range(5)]
haircolor = [Const(f'haircolor_{i}', HairColor) for i in range(5)]

s = Solver()

# Add distinctness constraints for each attribute
for lst in [name, birthday, mother, occupation, haircolor]:
    s.add(Distinct(lst))

# Apply clues
s.add(birthday[4] == mar)  # Clue 1
s.add(birthday[0] == feb)  # Clue 2

# Clue 3: Eric is a doctor
s.add(Or([And(name[i] == Eric, occupation[i] == doctor) for i in range(5)]))

s.add(mother[2] == Janelle)  # Clue 4

# Clue 5: Artist has brown hair
for i in range(5):
    s.add(Implies(occupation[i] == artist, haircolor[i] == brown))

s.add(occupation[3] == artist)  # Clue 6
s.add(haircolor[3] == brown)    # Clue 6

# Clue 7: Penny is left of black hair
penny_house = Int('penny_house')
black_house = Int('black_house')
s.add(And(0 <= penny_house, penny_house <= 4))
s.add(And(0 <= black_house, black_house <= 4))
s.add(Or([And(mother[i] == Penny, penny_house == i) for i in range(5)]))
s.add(Or([And(haircolor[i] == black, black_house == i) for i in range(5)]))
s.add(penny_house < black_house)

# Clue 8: Peter has black hair
s.add(Or([And(name[i] == Peter, haircolor[i] == black) for i in range(5)]))

# Clue 9: Gray hair is a teacher
for i in range(5):
    s.add(Implies(haircolor[i] == gray, occupation[i] == teacher))

# Clue 10: Alice's mother is Kailyn
s.add(Or([And(name[i] == Alice, mother[i] == Kailyn) for i in range(5)]))

# Clue 11: Arnold is right of September birthday
sept_house = Int('sept_house')
arnold_house = Int('arnold_house')
s.add(And(0 <= sept_house, sept_house <= 4))
s.add(And(0 <= arnold_house, arnold_house <= 4))
s.add(Or([And(birthday[i] == sept, sept_house == i) for i in range(5)]))
s.add(Or([And(name[i] == Arnold, arnold_house == i) for i in range(5)]))
s.add(sept_house < arnold_house)

# Clue 12: Brown hair has birthday January
for i in range(5):
    s.add(Implies(haircolor[i] == brown, birthday[i] == jan))

# Clue 13: Arnold has blonde hair
s.add(Or([And(name[i] == Arnold, haircolor[i] == blonde) for i in range(5)]))

# Clue 14: Black hair's mother is Holly
s.add(Or([And(haircolor[i] == black, mother[i] == Holly) for i in range(5)]))

# Clue 15: Peter is a lawyer
s.add(Or([And(name[i] == Peter, occupation[i] == lawyer) for i in range(5)]))

# Clue 16: September birthday is left of Kailyn's mother (Alice's house)
kailyn_house = Int('kailyn_house')
s.add(And(0 <= kailyn_house, kailyn_house <= 4))
s.add(Or([And(mother[i] == Kailyn, kailyn_house == i) for i in range(5)]))
s.add(sept_house < kailyn_house)

# Clue 17: Alice has gray hair
s.add(Or([And(name[i] == Alice, haircolor[i] == gray) for i in range(5)]))

# Check for solution
if s.check() == sat:
    model = s.model()
    rows = []
    for i in range(5):
        house_num = i + 1
        n = model[name[i]]
        b = model[birthday[i]]
        m = model[mother[i]]
        o = model[occupation[i]]
        h = model[haircolor[i]]
        rows.append([
            str(house_num),
            n.decl().name(),
            b.decl().name(),
            m.decl().name(),
            o.decl().name(),
            h.decl().name()
        ])
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")