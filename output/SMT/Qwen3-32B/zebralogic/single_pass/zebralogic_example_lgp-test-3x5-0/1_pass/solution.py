from z3 import *
import json

solver = Solver()

# Define possible values for each attribute
names_list = ["Peter", "Arnold", "Eric"]
bookgenre_list = ["science fiction", "mystery", "romance"]
smoothie_list = ["watermelon", "desert", "cherry"]
birthday_list = ["april", "jan", "sept"]
height_list = ["average", "very short", "short"]

# Create variables for each attribute and house
# Houses are 1, 2, 3. Variables are for each house in order 0,1,2 (house 1, 2, 3)

# Name variables (0: Peter, 1: Arnold, 2: Eric)
name = [Int(f'name_{i+1}') for i in range(3)]
for v in name:
    solver.add(And(0 <= v, v <= 2))
solver.add(Distinct(name))

# BookGenre variables (0: sci-fi, 1: mystery, 2: romance)
bookgenre = [Int(f'bookgenre_{i+1}') for i in range(3)]
for v in bookgenre:
    solver.add(And(0 <= v, v <= 2))
solver.add(Distinct(bookgenre))

# Smoothie variables (0: watermelon, 1: desert, 2: cherry)
smoothie = [Int(f'smoothie_{i+1}') for i in range(3)]
for v in smoothie:
    solver.add(And(0 <= v, v <= 2))
solver.add(Distinct(smoothie))

# Birthday variables (0: april, 1: jan, 2: sept)
birthday = [Int(f'birthday_{i+1}') for i in range(3)]
for v in birthday:
    solver.add(And(0 <= v, v <= 2))
solver.add(Distinct(birthday))

# Height variables (0: average, 1: very short, 2: short)
height = [Int(f'height_{i+1}') for i in range(3)]
for v in height:
    solver.add(And(0 <= v, v <= 2))
solver.add(Distinct(height))

# Now add the clues as constraints

# Clue 7: Eric is in the first house (name_1 == 2)
solver.add(name[0] == 2)

# Clue 9: Watermelon lover is Eric (house 1's smoothie is 0)
solver.add(smoothie[0] == 0)

# Clue 8: Watermelon lover (house 1) is short (height_1 == 2)
solver.add(height[0] == 2)

# Clue 1: Cherry (2) not in house 2 (smoothie_2 != 2)
solver.add(smoothie[1] != 2)

# Clue 2: Arnold (name=1) has mystery (bookgenre=1)
for i in range(3):
    solver.add(Implies(name[i] == 1, bookgenre[i] == 1))

# Clue 5: mystery (bookgenre=1) has birthday sept (2)
for i in range(3):
    solver.add(Implies(bookgenre[i] == 1, birthday[i] == 2))

# Clue 3: jan (1) not in first house (birthday_1 != 1)
solver.add(birthday[0] != 1)

# Clue 4: very short (height=1) has romance (bookgenre=2)
for i in range(3):
    solver.add(Implies(height[i] == 1, bookgenre[i] == 2))

# Clue 6: average height (0) is desert lover (1)
for i in range(3):
    solver.add(Implies(height[i] == 0, smoothie[i] == 1))

if solver.check() == sat:
    model = solver.model()
    # Now extract the values for each house
    solution_rows = []
    for i in range(3):  # i is 0,1,2 corresponding to house 1,2,3
        house_num = i + 1
        # Get the indices for each attribute
        n = model[name[i]].as_long()
        bg = model[bookgenre[i]].as_long()
        s = model[smoothie[i]].as_long()
        b = model[birthday[i]].as_long()
        h = model[height[i]].as_long()
        # Convert indices to strings
        name_str = names_list[n]
        bg_str = bookgenre_list[bg]
        s_str = smoothie_list[s]
        b_str = birthday_list[b]
        h_str = height_list[h]
        solution_rows.append([str(house_num), name_str, bg_str, s_str, b_str, h_str])
    # The solution is in order of houses 1, 2, 3
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": solution_rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")