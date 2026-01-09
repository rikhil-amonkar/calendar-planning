import json
from constraint import Problem, AllDifferentConstraint

def var_name(prefix, value):
    return f"{prefix}_{value.replace(' ', '_')}"

# Define attributes
houses = range(1, 7)

Names = ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice']
Animals = ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog']
Occupations = ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor']
Sports = ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming']
Heights = ['average', 'tall', 'short', 'very short', 'very tall', 'super tall']

# Create variable mappings
N_vars = {name: var_name("N", name) for name in Names}
A_vars = {animal: var_name("A", animal) for animal in Animals}
O_vars = {occ: var_name("O", occ) for occ in Occupations}
S_vars = {sport: var_name("S", sport) for sport in Sports}
H_vars = {height: var_name("H", height) for height in Heights}

problem = Problem()

# Add variables with domain 1..6
for v in list(N_vars.values()) + list(A_vars.values()) + list(O_vars.values()) + list(S_vars.values()) + list(H_vars.values()):
    problem.addVariable(v, houses)

# AllDifferent constraints for each category
problem.addConstraint(AllDifferentConstraint(), list(N_vars.values()))
problem.addConstraint(AllDifferentConstraint(), list(A_vars.values()))
problem.addConstraint(AllDifferentConstraint(), list(O_vars.values()))
problem.addConstraint(AllDifferentConstraint(), list(S_vars.values()))
problem.addConstraint(AllDifferentConstraint(), list(H_vars.values()))

# Helper functions for constraints
def eq(a, b):
    problem.addConstraint(lambda x, y: x == y, (a, b))

def left_of(a, b):
    problem.addConstraint(lambda x, y: x < y, (a, b))

def right_of(a, b):
    problem.addConstraint(lambda x, y: x > y, (a, b))

def directly_left_of(a, b):
    problem.addConstraint(lambda x, y: x + 1 == y, (a, b))

def set_pos(var, pos):
    problem.addConstraint(lambda x: x == pos, (var,))

# Apply clues as constraints

# 1. The person who is an engineer is the dog owner.
eq(O_vars['engineer'], A_vars['dog'])

# 2. The person who has an average height is somewhere to the left of the person who is short.
left_of(H_vars['average'], H_vars['short'])

# 3. The person who has an average height is directly left of the rabbit owner.
directly_left_of(H_vars['average'], A_vars['rabbit'])

# 4. The person who is tall is somewhere to the left of the person who is very short.
left_of(H_vars['tall'], H_vars['very short'])

# 5. Arnold is the cat lover.
eq(N_vars['Arnold'], A_vars['cat'])

# 6. The person who keeps horses is the person who is a teacher.
eq(A_vars['horse'], O_vars['teacher'])

# 7. Carol is the person who loves soccer.
eq(N_vars['Carol'], S_vars['soccer'])

# 8. The person who is tall is the person who loves volleyball.
eq(H_vars['tall'], S_vars['volleyball'])

# 9. The person who is a lawyer is in the fifth house.
set_pos(O_vars['lawyer'], 5)

# 10. The person who loves tennis is the person who is a teacher.
eq(S_vars['tennis'], O_vars['teacher'])

# 11. The person who has an average height is the person who loves swimming.
eq(H_vars['average'], S_vars['swimming'])

# 12. The person who loves baseball is directly left of the person who is an engineer.
directly_left_of(S_vars['baseball'], O_vars['engineer'])

# 13. Peter is the person who is a nurse.
eq(N_vars['Peter'], O_vars['nurse'])

# 14. Bob is somewhere to the right of the person who is an artist.
right_of(N_vars['Bob'], O_vars['artist'])

# 15. The person who is a teacher is directly left of the person who loves soccer.
directly_left_of(O_vars['teacher'], S_vars['soccer'])

# 16. The rabbit owner is Alice.
eq(A_vars['rabbit'], N_vars['Alice'])

# 17. The fish enthusiast is Carol.
eq(A_vars['fish'], N_vars['Carol'])

# 18. The person who loves baseball is in the first house.
set_pos(S_vars['baseball'], 1)

# 19. The cat lover is somewhere to the right of the person who is very short.
right_of(A_vars['cat'], H_vars['very short'])

# 20. The person who is super tall is in the fifth house.
set_pos(H_vars['super tall'], 5)

# Solve
solution = problem.getSolution()
if solution is None:
    print(json.dumps({"solution": {"header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"], "rows": []}}, indent=2))
    raise SystemExit

# Build output rows per house 1..6
def value_at_house(mapping, house):
    for k, v in mapping.items():
        if solution[v] == house:
            return k
    return None

rows = []
for h in range(1, 7):
    name = value_at_house(N_vars, h)
    animal = value_at_house(A_vars, h)
    occupation = value_at_house(O_vars, h)
    sport = value_at_house(S_vars, h)
    height = value_at_house(H_vars, h)
    rows.append([str(h), name, animal, occupation, sport, height])

output = {
    "solution": {
        "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
        "rows": rows
    }
}

print(json.dumps(output, ensure_ascii=False, indent=2))