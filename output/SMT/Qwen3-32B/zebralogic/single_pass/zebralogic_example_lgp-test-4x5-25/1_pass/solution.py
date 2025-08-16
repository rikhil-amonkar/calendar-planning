from z3 import *
import json

# Define the problem
houses = 4

# Create variables for each house (0-based index)
names = [Int('names_%d' % i) for i in range(houses)]
styles = [Int('styles_%d' % i) for i in range(houses)]
hair_colors = [Int('hair_colors_%d' % i) for i in range(houses)]
children = [Int('children_%d' % i) for i in range(houses)]
book_genres = [Int('book_genres_%d' % i) for i in range(houses)]

s = Solver()

# Add constraints for each attribute to be permutations (0-3, distinct)
for attr in [names, styles, hair_colors, children, book_genres]:
    for i in range(houses):
        s.add(And(attr[i] >= 0, attr[i] < houses))
    s.add(Distinct(*attr))

# Add clues
# Clue 1: Craftsman (0) in house 3 (index 2)
s.add(styles[2] == 0)

# Clue 2: Alice (3) loves romance (2)
for i in range(houses):
    s.add(Implies(names[i] == 3, book_genres[i] == 2))

# Clue 3: Brown hair (3) in house 4 (index 3)
s.add(hair_colors[3] == 3)

# Clue 4: Child Samantha (3) in house 4 (index 3)
s.add(children[3] == 3)

# Clue 5: Ranch (3) is to the right of red hair (0)
for i in range(houses):
    for j in range(houses):
        s.add(Implies(And(hair_colors[i] == 0, styles[j] == 3), j > i))

# Clue 6: Peter (1) has child Bella (0)
for i in range(houses):
    s.add(Implies(names[i] == 1, children[i] == 0))

# Clue 7: Arnold (0) has red hair (0)
for i in range(houses):
    s.add(Implies(names[i] == 0, hair_colors[i] == 0))

# Clue 8: Alice (3) lives in colonial (1)
for i in range(houses):
    s.add(Implies(names[i] == 3, styles[i] == 1))

# Clue 9: Black hair (2) in house 2 (index 1)
s.add(hair_colors[1] == 2)

# Clue 10: Peter (1) loves fantasy (1)
for i in range(houses):
    s.add(Implies(names[i] == 1, book_genres[i] == 1))

# Clue 11: Arnold (0) has child Meredith (2)
for i in range(houses):
    s.add(Implies(names[i] == 0, children[i] == 2))

# Clue 12: Eric (2) has black hair (2)
for i in range(houses):
    s.add(Implies(names[i] == 2, hair_colors[i] == 2))

# Clue 13: Arnold (0) loves science fiction (3)
for i in range(houses):
    s.add(Implies(names[i] == 0, book_genres[i] == 3))

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    # Mapping from codes to strings
    name_map = {0: 'Arnold', 1: 'Peter', 2: 'Eric', 3: 'Alice'}
    style_map = {0: 'craftsman', 1: 'colonial', 2: 'victorian', 3: 'ranch'}
    hair_color_map = {0: 'red', 1: 'blonde', 2: 'black', 3: 'brown'}
    children_map = {0: 'Bella', 1: 'Fred', 2: 'Meredith', 3: 'Samantha'}
    book_genre_map = {0: 'mystery', 1: 'fantasy', 2: 'romance', 3: 'science fiction'}
    
    # Generate the rows
    rows = []
    for i in range(houses):
        house_num = str(i + 1)
        name_code = model.eval(names[i]).as_long()
        style_code = model.eval(styles[i]).as_long()
        hair_code = model.eval(hair_colors[i]).as_long()
        child_code = model.eval(children[i]).as_long()
        book_code = model.eval(book_genres[i]).as_long()
        rows.append([
            house_num,
            name_map[name_code],
            style_map[style_code],
            hair_color_map[hair_code],
            children_map[child_code],
            book_genre_map[book_code]
        ])
    
    # Output JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")