from z3 import *

# Define EnumSorts
Names, (Arnold, Peter, Carol, Alice, Bob, Eric) = EnumSort('Names', ['Arnold', 'Peter', 'Carol', 'Alice', 'Bob', 'Eric'])
Children, (AliceC, Timothy, Bella, Meredith, Fred, Samantha) = EnumSort('Children', ['Alice', 'Timothy', 'Bella', 'Meredith', 'Fred', 'Samantha'])
Smoothies, (desert, cherry, watermelon, blueberry, lime, dragonfruit) = EnumSort('Smoothies', ['desert', 'cherry', 'watermelon', 'blueberry', 'lime', 'dragonfruit'])

# Create solver
s = Solver()

# Create variables for each house (0-5 for houses 1-6)
name = [Const(f'name_{i}', Names) for i in range(6)]
child = [Const(f'child_{i}', Children) for i in range(6)]
smoothie = [Const(f'smoothie_{i}', Smoothies) for i in range(6)]

# Add uniqueness constraints
s.add(Distinct(name))
s.add(Distinct(child))
s.add(Distinct(smoothie))

# Add clues
# Clue 1: Fred's parent and Desert are adjacent
for i in range(6):
    for j in range(6):
        s.add(Implies(And(child[i] == Fred, smoothie[j] == desert), Or(j == i-1, j == i+1)))

# Clue 2: Blueberry is left of Fred's parent
for i in range(6):
    for j in range(6):
        s.add(Implies(And(smoothie[i] == blueberry, child[j] == Fred), i < j))

# Clue 3: Alice not in fifth house (index 4)
s.add(name[4] != Alice)

# Clue 4: Samantha's parent not in second house (index 1)
for i in range(6):
    s.add(Implies(child[i] == Samantha, i != 1))

# Clue 5: Watermelon is right of Cherry
for i in range(6):
    for j in range(6):
        s.add(Implies(And(smoothie[i] == watermelon, smoothie[j] == cherry), i > j))

# Clue 6: Alice's child is Alice
for i in range(6):
    s.add(Implies(name[i] == Alice, child[i] == AliceC))

# Clue 7: Alice's smoothie is Watermelon
for i in range(6):
    s.add(Implies(name[i] == Alice, smoothie[i] == watermelon))

# Clue 8: Peter is right of Samantha's parent
for i in range(6):
    for j in range(6):
        s.add(Implies(And(name[i] == Peter, child[j] == Samantha), i > j))

# Clue 9: Arnold not in second house (index 1)
s.add(name[1] != Arnold)

# Clue 10: Bob's child is Timothy
for i in range(6):
    s.add(Implies(name[i] == Bob, child[i] == Timothy))

# Clue 11: Arnold directly left of Carol
s.add(Or([And(name[i] == Arnold, name[i+1] == Carol) for i in range(5)]))

# Clue 12: Cherry directly left of Samantha's parent
s.add(Or([And(smoothie[i] == cherry, child[i+1] == Samantha) for i in range(5)]))

# Clue 13: child[5] is Meredith
s.add(child[5] == Meredith)

# Clue 14: Dragonfruit smoothie has child Meredith
for i in range(6):
    s.add(Implies(smoothie[i] == dragonfruit, child[i] == Meredith))
s.add(smoothie[5] == dragonfruit)

# Solve
if s.check() == sat:
    m = s.model()
    # Mapping enums to strings
    name_str = {
        Arnold: 'Arnold',
        Peter: 'Peter',
        Carol: 'Carol',
        Alice: 'Alice',
        Bob: 'Bob',
        Eric: 'Eric'
    }
    child_str = {
        AliceC: 'Alice',
        Timothy: 'Timothy',
        Bella: 'Bella',
        Meredith: 'Meredith',
        Fred: 'Fred',
        Samantha: 'Samantha'
    }
    smoothie_str = {
        desert: 'desert',
        cherry: 'cherry',
        watermelon: 'watermelon',
        blueberry: 'blueberry',
        lime: 'lime',
        dragonfruit: 'dragonfruit'
    }
    rows = []
    for i in range(6):
        house_num = i + 1
        n = name_str[m[name[i]]]
        c = child_str[m[child[i]]]
        s_i = smoothie_str[m[smoothie[i]]]
        rows.append([str(house_num), n, c, s_i])
    solution = {
        "solution": {
            "header": ["House", "Name", "Children", "Smoothie"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")