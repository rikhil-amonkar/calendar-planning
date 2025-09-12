from z3 import *
import json

# Define the variables
houses = [1, 2]
names = ['Arnold', 'Eric']
occupations = ['engineer', 'doctor']
birthdays = ['april', 'sept']
house_styles = ['victorian', 'colonial']
heights = ['very short', 'short']
cigars = ['pall mall', 'prince']

# Create dictionaries to map variables to Z3 variables
name_vars = {h: Int(f'name_{h}') for h in houses}
occupation_vars = {h: Int(f'occupation_{h}') for h in houses}
birthday_vars = {h: Int(f'birthday_{h}') for h in houses}
house_style_vars = {h: Int(f'house_style_{h}') for h in houses}
height_vars = {h: Int(f'height_{h}') for h in houses}
cigar_vars = {h: Int(f'cigar_{h}') for h in houses}

# Create a solver instance
solver = Solver()

# Add constraints for unique values per category
for h in houses:
    solver.add(name_vars[h] >= 0, name_vars[h] < len(names))
    solver.add(occupation_vars[h] >= 0, occupation_vars[h] < len(occupations))
    solver.add(birthday_vars[h] >= 0, birthday_vars[h] < len(birthdays))
    solver.add(house_style_vars[h] >= 0, house_style_vars[h] < len(house_styles))
    solver.add(height_vars[h] >= 0, height_vars[h] < len(heights))
    solver.add(cigar_vars[h] >= 0, cigar_vars[h] < len(cigars))

# Ensure all values are unique across houses
solver.add(Distinct([name_vars[h] for h in houses]))
solver.add(Distinct([occupation_vars[h] for h in houses]))
solver.add(Distinct([birthday_vars[h] for h in houses]))
solver.add(Distinct([house_style_vars[h] for h in houses]))
solver.add(Distinct([height_vars[h] for h in houses]))
solver.add(Distinct([cigar_vars[h] for h in houses]))

# Add the clues as constraints
# Clue 1: The person who is an engineer is in the first house.
solver.add(occupation_vars[1] == occupations.index('engineer'))

# Clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
solver.add(Or(
    And(birthday_vars[1] == birthdays.index('april'), occupation_vars[2] == occupations.index('doctor')),
    And(birthday_vars[2] == birthdays.index('april'), occupation_vars[1] == occupations.index('doctor'))
))

# Clue 3: The person living in a colonial-style house is the person who is an engineer.
solver.add(house_style_vars[1] == house_styles.index('colonial'))

# Clue 4: The person who is very short is the person who is an engineer.
solver.add(height_vars[1] == heights.index('very short'))

# Clue 5: The person who is short is the person partial to Pall Mall.
solver.add(height_vars[2] == heights.index('short'))
solver.add(cigar_vars[2] == cigars.index('pall mall'))

# Clue 6: The person who is an engineer is Eric.
solver.add(name_vars[1] == names.index('Eric'))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            names[model[name_vars[h]].as_long()],
            occupations[model[occupation_vars[h]].as_long()],
            birthdays[model[birthday_vars[h]].as_long()],
            house_styles[model[house_style_vars[h]].as_long()],
            heights[model[height_vars[h]].as_long()],
            cigars[model[cigar_vars[h]].as_long()]
        ]
        solution["solution"]["rows"].append(row)
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")