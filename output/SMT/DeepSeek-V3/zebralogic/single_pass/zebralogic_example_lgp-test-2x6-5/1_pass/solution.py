import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the attributes for each house
houses = [1, 2]
names = ['Arnold', 'Eric']
occupations = ['engineer', 'doctor']
birthdays = ['april', 'sept']
house_styles = ['victorian', 'colonial']
heights = ['very short', 'short']
cigars = ['pall mall', 'prince']

# Create variables for each attribute in each house
name = {house: String(f'name_{house}') for house in houses}
occupation = {house: String(f'occupation_{house}') for house in houses}
birthday = {house: String(f'birthday_{house}') for house in houses}
house_style = {house: String(f'house_style_{house}') for house in houses}
height = {house: String(f'height_{house}') for house in houses}
cigar = {house: String(f'cigar_{house}') for house in houses}

# Add constraints for uniqueness within each attribute
for house1 in houses:
    for house2 in houses:
        if house1 < house2:
            s.add(name[house1] != name[house2])
            s.add(occupation[house1] != occupation[house2])
            s.add(birthday[house1] != birthday[house2])
            s.add(house_style[house1] != house_style[house2])
            s.add(height[house1] != height[house2])
            s.add(cigar[house1] != cigar[house2])

# Each attribute must be one of the allowed values
for house in houses:
    s.add(Or([name[house] == n for n in names]))
    s.add(Or([occupation[house] == o for o in occupations]))
    s.add(Or([birthday[house] == b for b in birthdays]))
    s.add(Or([house_style[house] == h for h in house_styles]))
    s.add(Or([height[house] == h for h in heights]))
    s.add(Or([cigar[house] == c for c in cigars]))

# Apply the clues
# Clue 1: The person who is an engineer is in the first house.
s.add(occupation[1] == 'engineer')

# Clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
s.add(Or(
    And(birthday[1] == 'april', occupation[2] == 'doctor'),
    And(birthday[2] == 'april', occupation[1] == 'doctor')
))

# Clue 3: The person living in a colonial-style house is the person who is an engineer.
s.add(house_style[1] == 'colonial')  # Since engineer is in house 1

# Clue 4: The person who is very short is the person who is an engineer.
s.add(height[1] == 'very short')

# Clue 5: The person who is short is the person partial to Pall Mall.
for house in houses:
    s.add(Implies(height[house] == 'short', cigar[house] == 'pall mall'))

# Clue 6: The person who is an engineer is Eric.
s.add(name[1] == 'Eric')

# Solve the model
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
            "rows": []
        }
    }
    for house in sorted(houses):
        row = [
            str(house),
            str(model.eval(name[house])),
            str(model.eval(occupation[house])),
            str(model.eval(birthday[house])),
            str(model.eval(house_style[house])),
            str(model.eval(height[house])),
            str(model.eval(cigar[house]))
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")