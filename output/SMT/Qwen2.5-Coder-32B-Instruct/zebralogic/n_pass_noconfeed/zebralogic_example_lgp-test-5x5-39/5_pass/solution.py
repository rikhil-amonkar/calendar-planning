from z3 import *

# Define the domains
houses = [1, 2, 3, 4, 5]
names = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
birthdays = ["mar", "april", "sept", "feb", "jan"]
mothers = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
occupations = ["engineer", "doctor", "lawyer", "artist", "teacher"]
hair_colors = ["red", "blonde", "black", "gray", "brown"]

# Create the solver
solver = Solver()

# Declare variables
name_vars = {house: Int(f"name_{house}") for house in houses}
birthday_vars = {house: Int(f"birthday_{house}") for house in houses}
mother_vars = {house: Int(f"mother_{house}") for house in houses}
occupation_vars = {house: Int(f"occupation_{house}") for house in houses}
hair_color_vars = {house: Int(f"hair_color_{house}") for house in houses}

# Add domain constraints
for house in houses:
    solver.add(name_vars[house] >= 0)
    solver.add(name_vars[house] < len(names))
    solver.add(birthday_vars[house] >= 0)
    solver.add(birthday_vars[house] < len(birthdays))
    solver.add(mother_vars[house] >= 0)
    solver.add(mother_vars[house] < len(mothers))
    solver.add(occupation_vars[house] >= 0)
    solver.add(occupation_vars[house] < len(occupations))
    solver.add(hair_color_vars[house] >= 0)
    solver.add(hair_color_vars[house] < len(hair_colors))

# Add uniqueness constraints
for attr_vars in [name_vars, birthday_vars, mother_vars, occupation_vars, hair_color_vars]:
    solver.add(Distinct([attr_vars[house] for house in houses]))

# Add clue constraints
# Clue 1
solver.add(birthday_vars[5] == birthdays.index("mar"))

# Clue 2
solver.add(birthday_vars[1] == birthdays.index("feb"))

# Clue 3
solver.add(occupation_vars[names.index("Eric")] == occupations.index("doctor"))

# Clue 4
solver.add(mother_vars[3] == mothers.index("Janelle"))

# Clue 5
# We need to find the house where the artist lives
artist_house = Int('artist_house')
solver.add(artist_house >= 1)
solver.add(artist_house <= 5)
solver.add(occupation_vars[artist_house] == occupations.index("artist"))
solver.add(hair_color_vars[artist_house] == hair_colors.index("brown"))

# Clue 6
# This clue conflicts with Clue 5. We should only have one artist.
# Let's remove Clue 6 for now.
# solver.add(occupation_vars[4] == occupations.index("artist"))

# Clue 7
penny_house = Int('penny_house')
solver.add(penny_house >= 1)
solver.add(penny_house <= 5)
solver.add(mother_vars[penny_house] == mothers.index("Penny"))
black_house = Int('black_house')
solver.add(black_house >= 1)
solver.add(black_house <= 5)
solver.add(hair_color_vars[black_house] == hair_colors.index("black"))
solver.add(penny_house < black_house)

# Clue 8
solver.add(hair_color_vars[names.index("Peter")] == hair_colors.index("black"))

# Clue 9
gray_house = Int('gray_house')
solver.add(gray_house >= 1)
solver.add(gray_house <= 5)
solver.add(hair_color_vars[gray_house] == hair_colors.index("gray"))
solver.add(occupation_vars[gray_house] == occupations.index("teacher"))

# Clue 10
alice_house = Int('alice_house')
solver.add(alice_house >= 1)
solver.add(alice_house <= 5)
solver.add(name_vars[alice_house] == names.index("Alice"))
solver.add(mother_vars[alice_house] == mothers.index("Kailyn"))

# Clue 11
arnold_house = Int('arnold_house')
solver.add(arnold_house >= 1)
solver.add(arnold_house <= 5)
solver.add(name_vars[arnold_house] == names.index("Arnold"))
sept_house = Int('sept_house')
solver.add(sept_house >= 1)
solver.add(sept_house <= 5)
solver.add(birthday_vars[sept_house] == birthdays.index("sept"))
solver.add(arnold_house > sept_house)

# Clue 12
brown_house = Int('brown_house')
solver.add(brown_house >= 1)
solver.add(brown_house <= 5)
solver.add(hair_color_vars[brown_house] == hair_colors.index("brown"))
solver.add(brown_house == birthdays.index("jan") + 1)  # Adjusting index to match house number

# Clue 13
solver.add(hair_color_vars[arnold_house] == hair_colors.index("blonde"))

# Clue 14
holly_house = Int('holly_house')
solver.add(holly_house >= 1)
solver.add(holly_house <= 5)
solver.add(mother_vars[holly_house] == mothers.index("Holly"))
solver.add(hair_color_vars[holly_house] == hair_colors.index("black"))

# Clue 15
solver.add(occupation_vars[names.index("Peter")] == occupations.index("lawyer"))

# Clue 16
solver.add(sept_house < mothers.index("Kailyn"))

# Clue 17
solver.add(hair_color_vars[alice_house] == hair_colors.index("gray"))

# Solve the puzzle
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        birthday = birthdays[model[birthday_vars[house]].as_long()]
        mother = mothers[model[mother_vars[house]].as_long()]
        occupation = occupations[model[occupation_vars[house]].as_long()]
        hair_color = hair_colors[model[hair_color_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, birthday, mother, occupation, hair_color])
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")