import json
from z3 import *

# Define EnumSorts for the attributes
Name, (Arnold, Eric, Bob, Peter, Alice) = EnumSort('Name', ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice'])
Smoothie, (Desert, Watermelon, Lime, Cherry, Dragonfruit) = EnumSort('Smoothie', ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit'])
Nationality, (German, Swede, Norwegian, Dane, Brit) = EnumSort('Nationality', ['german', 'swede', 'norwegian', 'dane', 'brit'])

# Create variables for each house (1-5)
names = [Const(f'name_{i+1}', Name) for i in range(5)]
smoothies = [Const(f'smoothie_{i+1}', Smoothie) for i in range(5)]
nationalities = [Const(f'nationality_{i+1}', Nationality) for i in range(5)]

s = Solver()

# Add uniqueness constraints
s.add(Distinct(names))
s.add(Distinct(smoothies))
s.add(Distinct(nationalities))

# Add specific constraints from the puzzle
# Clue 2: Dragonfruit in house 2 (index 1)
s.add(smoothies[1] == Dragonfruit)

# Clue 10: Alice in house 3 (index 2)
s.add(names[2] == Alice)

# Clue 11: Watermelon in house 3 (index 2)
s.add(smoothies[2] == Watermelon)

# Clue 9: Alice is Norwegian (house 3, index 2)
s.add(nationalities[2] == Norwegian)

# Clue 3: Peter not in first house (index 0)
s.add(names[0] != Peter)

# Clue 8: Bob is Dane
for i in range(5):
    s.add(Implies(names[i] == Bob, nationalities[i] == Dane))

# Clue 6: Swede in house 1 (index 0)
s.add(nationalities[0] == Swede)

# Clue 4: Dane and Brit adjacent
for i in range(5):
    adjacent_brit = []
    if i > 0:
        adjacent_brit.append(nationalities[i-1] == Brit)
    if i < 4:
        adjacent_brit.append(nationalities[i+1] == Brit)
    cond = Or(adjacent_brit)
    s.add(Implies(names[i] == Bob, cond))

# Clue 7: Two houses between Lime and Dane (Bob's house)
for i in range(5):
    lime_pos = []
    if i - 3 >= 0:
        lime_pos.append(smoothies[i - 3] == Lime)
    if i + 3 < 5:
        lime_pos.append(smoothies[i + 3] == Lime)
    cond = Or(lime_pos)
    s.add(Implies(names[i] == Bob, cond))

# Clue 1: Eric is to the right of Dragonfruit (house 2)
for i in range(5):
    s.add(Implies(names[i] == Eric, i >= 2))

# Clue 5: Desert not in fifth house (index 4)
s.add(smoothies[4] != Desert)

if s.check() == sat:
    model = s.model()
    rows = []
    for i in range(5):
        house_num = str(i + 1)
        name = str(model.eval(names[i]))
        smoothie = str(model.eval(smoothies[i]))
        nat = str(model.eval(nationalities[i]))
        rows.append([house_num, name, smoothie, nat])
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")