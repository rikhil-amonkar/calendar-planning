from z3 import *

# Define the lists for each category
name_list = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
style_list = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
music_list = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
hobby_list = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']

# Create solver
s = Solver()

# Create variables for each house (0-5)
names = [Int(f'names_{i}') for i in range(6)]
styles = [Int(f'styles_{i}') for i in range(6)]
music = [Int(f'music_{i}') for i in range(6)]
hobbies = [Int(f'hobbies_{i}') for i in range(6)]

# Add constraints for distinct values and ranges
for arr in [names, styles, music, hobbies]:
    s.add(Distinct(arr))
    for var in arr:
        s.add(And(0 <= var, var <= 5))

# Clue 1: Rock music is in the fifth house (index 4)
s.add(music[4] == 5)  # rock is index 5

# Clue 2: classical and woodworking are next to each other
clue2 = Or(
    [And(music[i] == 4, hobbies[i+1] == 3) for i in range(5)] +  # classical (4) and woodworking (3)
    [And(music[i+1] == 4, hobbies[i] == 3) for i in range(5)]
)
s.add(clue2)

# Clue 3: Mediterranean (0) style implies hip hop (1) music
for i in range(6):
    s.add(Implies(styles[i] == 0, music[i] == 1))

# Clue 4: Arnold (2) and Victorian (5) are 3 apart
A = Int('A')
V = Int('V')
s.add(A == Sum([If(names[i] == 2, i, 0) for i in range(6)]))
s.add(V == Sum([If(styles[i] == 5, i, 0) for i in range(6)]))
s.add(Abs(A - V) == 3)

# Clue 5: Jazz (3) is directly left of Eric (0)
s.add(Or([And(music[i] == 3, names[i+1] == 0) for i in range(5)]))

# Clue 6: Hip hop (1) is left of knitting (5)
H = Int('H')
K = Int('K')
s.add(H == Sum([If(music[i] == 1, i, 0) for i in range(6)]))
s.add(K == Sum([If(hobbies[i] == 5, i, 0) for i in range(6)]))
s.add(H < K)

# Clue 7: Carol (3) loves hip hop (1)
for i in range(6):
    s.add(Implies(names[i] == 3, music[i] == 1))

# Clue 8: Arnold (2) has Craftsman (2) style
for i in range(6):
    s.add(Implies(names[i] == 2, styles[i] == 2))

# Clue 9: Eric (0) has Ranch (3) style
for i in range(6):
    s.add(Implies(names[i] == 0, styles[i] == 3))

# Clue 10: Woodworking (3) is in Victorian (5)
for i in range(6):
    s.add(Implies(hobbies[i] == 3, styles[i] == 5))

# Clue 11: Country (0) in first house (index 0)
s.add(music[0] == 0)

# Clue 12: Painter (1) and Colonial (4) are 2 apart
P = Int('P')
C = Int('C')
s.add(P == Sum([If(hobbies[i] == 1, i, 0) for i in range(6)]))
s.add(C == Sum([If(styles[i] == 4, i, 0) for i in range(6)]))
s.add(Abs(P - C) == 2)

# Clue 13: Alice (1) has Photography (2)
for i in range(6):
    s.add(Implies(names[i] == 1, hobbies[i] == 2))

# Clue 14: Eric (0) has Gardening (4)
for i in range(6):
    s.add(Implies(names[i] == 0, hobbies[i] == 4))

# Clue 15: Bob (5) in third house (index 2)
s.add(names[2] == 5)

# Check for solution
if s.check() == sat:
    m = s.model()
    solution = []
    for i in range(6):
        house_num = i + 1
        name_idx = m.eval(names[i]).as_long()
        name = name_list[name_idx]
        style_idx = m.eval(styles[i]).as_long()
        style = style_list[style_idx]
        music_idx = m.eval(music[i]).as_long()
        music_genre = music_list[music_idx]
        hobby_idx = m.eval(hobbies[i]).as_long()
        hobby = hobby_list[hobby_idx]
        solution.append([str(house_num), name, style, music_genre, hobby])
    json_output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
            "rows": solution
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")