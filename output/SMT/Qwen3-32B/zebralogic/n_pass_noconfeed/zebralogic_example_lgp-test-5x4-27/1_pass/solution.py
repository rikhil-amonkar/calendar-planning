from z3 import *
import json

# Define EnumSorts
Names, (Peter, Alice, Eric, Bob, Arnold) = EnumSort('Names', ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold'])
Birthdays, (jan, feb, mar, april, sept) = EnumSort('Birthdays', ['jan', 'feb', 'mar', 'april', 'sept'])
Cigars, (pall_mall, prince, dunhill, blends, blue_master) = EnumSort('Cigars', ['pall mall', 'prince', 'dunhill', 'blends', 'blue master'])
Drinks, (water, coffee, tea, milk, root_beer) = EnumSort('Drinks', ['water', 'coffee', 'tea', 'milk', 'root beer'])

# Create variables for each house (0-based index, 0 to 4)
name = [Const(f'name_{i}', Names) for i in range(5)]
birthday = [Const(f'birthday_{i}', Birthdays) for i in range(5)]
cigar = [Const(f'cigar_{i}', Cigars) for i in range(5)]
drink = [Const(f'drink_{i}', Drinks) for i in range(5)]

s = Solver()

# Add uniqueness constraints for each attribute
s.add(Distinct(name))
s.add(Distinct(birthday))
s.add(Distinct(cigar))
s.add(Distinct(drink))

# Add clues as constraints

# Clue 1: Root beer lover is Eric.
for i in range(5):
    s.add(Implies(drink[i] == root_beer, name[i] == Eric))

# Clue 2: Pall Mall smoker is in the third house (index 2)
s.add(cigar[2] == pall_mall)

# Clue 3: Bob's birthday is April.
for i in range(5):
    s.add(Implies(name[i] == Bob, birthday[i] == april))

# Clue 4: Dunhill smoker has birthday March.
for i in range(5):
    s.add(Implies(cigar[i] == dunhill, birthday[i] == mar))

# Clue 5: Peter is to the right of root beer lover.
for i in range(5):
    for j in range(5):
        s.add(Implies(And(drink[i] == root_beer, name[j] == Peter), j > i))

# Clue 6: One house between birthday jan and Peter.
for i in range(5):
    for j in range(5):
        s.add(Implies(And(birthday[i] == jan, name[j] == Peter), Or(j == i + 2, j == i - 2)))

# Clue 7: Blends smoker has birthday February.
for i in range(5):
    s.add(Implies(cigar[i] == blends, birthday[i] == feb))

# Clue 8: Birthday feb is in house 2 (index 1)
s.add(birthday[1] == feb)

# Clue 9: Arnold is directly left of Peter.
for i in range(4):  # 0 to 3
    s.add(Implies(name[i] == Arnold, name[i + 1] == Peter))

# Clue 10: Milk drinker not in fifth house (index 4)
s.add(drink[4] != milk)

# Clue 11: Blue Master smoker drinks coffee.
for i in range(5):
    s.add(Implies(cigar[i] == blue_master, drink[i] == coffee))

# Clue 12: One house between tea and coffee drinkers.
for i in range(5):
    for j in range(5):
        cond = Or(And(drink[i] == tea, drink[j] == coffee), And(drink[i] == coffee, drink[j] == tea))
        s.add(Implies(cond, Or(j == i + 2, i == j + 2)))

# Clue 13: Eric is in third house (index 2)
s.add(name[2] == Eric)
s.add(drink[2] == root_beer)  # From clue 1
s.add(cigar[2] == pall_mall)  # From clue 2

# Solve
if s.check() == sat:
    model = s.model()
    
    # Create mappings from Enum constants to strings
    name_to_str = {Peter: 'Peter', Alice: 'Alice', Eric: 'Eric', Bob: 'Bob', Arnold: 'Arnold'}
    birthday_to_str = {jan: 'jan', feb: 'feb', mar: 'mar', april: 'april', sept: 'sept'}
    cigar_to_str = {pall_mall: 'pall mall', prince: 'prince', dunhill: 'dunhill', blends: 'blends', blue_master: 'blue master'}
    drink_to_str = {water: 'water', coffee: 'coffee', tea: 'tea', milk: 'milk', root_beer: 'root beer'}
    
    # Generate rows
    rows = []
    for i in range(5):
        house_num = i + 1
        n = model.evaluate(name[i])
        b = model.evaluate(birthday[i])
        c = model.evaluate(cigar[i])
        d = model.evaluate(drink[i])
        row = [
            str(house_num),
            name_to_str[n],
            birthday_to_str[b],
            cigar_to_str[c],
            drink_to_str[d],
        ]
        rows.append(row)
    
    # Build JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")