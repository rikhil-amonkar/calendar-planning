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
solver.add(hair_color_vars[occupations.index("artist")] == hair_colors.index("brown"))

# Clue 6
solver.add(occupation_vars[4] == occupations.index("artist"))

# Clue 7
solver.add(mother_vars[mothers.index("Penny")] < hair_color_vars[hair_colors.index("black")])

# Clue 8
solver.add(name_vars[names.index("Peter")] == hair_colors.index("black"))

# Clue 9
solver.add(hair_color_vars[hair_colors.index("gray")] == occupations.index("teacher"))

# Clue 10
solver.add(name_vars[names.index("Alice")] == mothers.index("Kailyn"))

# Clue 11
solver.add(names.index("Arnold") > birthday_vars[birthdays.index("sept")])

# Clue 12
solver.add(hair_color_vars[hair_colors.index("brown")] == birthdays.index("jan"))

# Clue 13
solver.add(name_vars[names.index("Arnold")] == hair_colors.index("blonde"))

# Clue 14
solver.add(mother_vars[mothers.index("Holly")] == hair_colors.index("black"))

# Clue 15
solver.add(name_vars[names.index("Peter")] == occupations.index("lawyer"))

# Clue 16
solver.add(birthday_vars[birthdays.index("sept")] < mothers.index("Kailyn"))

# Clue 17
solver.add(name_vars[names.index("Alice")] == hair_colors.index("gray"))

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