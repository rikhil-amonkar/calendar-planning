from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = range(1, 6)
names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
birthdays = ['april', 'feb', 'mar', 'jan', 'sept']
cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']

# Create dictionaries to map variables to their respective domains
name_vars = {house: Int(f'name_{house}') for house in houses}
birthday_vars = {house: Int(f'birthday_{house}') for house in houses}
cigar_vars = {house: Int(f'cigar_{house}') for house in houses}
drink_vars = {house: Int(f'drink_{house}') for house in houses}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([birthday_vars[house] for house in houses]))
solver.add(Distinct([cigar_vars[house] for house in houses]))
solver.add(Distinct([drink_vars[house] for house in houses]))

# Map names, birthdays, cigars, and drinks to integers
name_map = {name: i for i, name in enumerate(names)}
birthday_map = {birthday: i for i, birthday in enumerate(birthdays)}
cigar_map = {cigar: i for i, cigar in enumerate(cigars)}
drink_map = {drink: i for i, drink in enumerate(drinks)}

# Add clues as constraints
# Clue 1: The root beer lover is Eric.
solver.add(drink_vars[house] == drink_map['root beer'] for house in houses if name_vars[house] == name_map['Eric'])
solver.add(name_vars[house] == name_map['Eric'] for house in houses if drink_vars[house] == drink_map['root beer'])

# Clue 2: The person partial to Pall Mall is in the third house.
solver.add(cigar_vars[3] == cigar_map['pall mall'])

# Clue 3: The person whose birthday is in April is Bob.
solver.add(birthday_vars[house] == birthday_map['april'] for house in houses if name_vars[house] == name_map['Bob'])
solver.add(name_vars[house] == name_map['Bob'] for house in houses if birthday_vars[house] == birthday_map['april'])

# Clue 4: The Dunhill smoker is the person whose birthday is in March.
solver.add(cigar_vars[house] == cigar_map['dunhill'] for house in houses if birthday_vars[house] == birthday_map['mar'])
solver.add(birthday_vars[house] == birthday_map['mar'] for house in houses if cigar_vars[house] == cigar_map['dunhill'])

# Clue 5: Peter is somewhere to the right of the root beer lover.
solver.add(Or([And(name_vars[i] == name_map['Peter'], drink_vars[j] == drink_map['root beer']) for i in range(2, 6) for j in range(1, i)]))

# Clue 6: There is one house between the person whose birthday is in January and Peter.
solver.add(Or([And(birthday_vars[i] == birthday_map['jan'], name_vars[i+2] == name_map['Peter']) for i in range(1, 4)] +
              [And(birthday_vars[i] == birthday_map['jan'], name_vars[i-2] == name_map['Peter']) for i in range(3, 6)]))

# Clue 7: The person who smokes many unique blends is the person whose birthday is in February.
solver.add(cigar_vars[house] == cigar_map['blends'] for house in houses if birthday_vars[house] == birthday_map['feb'])
solver.add(birthday_vars[house] == birthday_map['feb'] for house in houses if cigar_vars[house] == cigar_map['blends'])

# Clue 8: The person whose birthday is in February is in the second house.
solver.add(birthday_vars[2] == birthday_map['feb'])

# Clue 9: Arnold is directly left of Peter.
solver.add(Or([And(name_vars[i] == name_map['Arnold'], name_vars[i+1] == name_map['Peter']) for i in range(1, 5)]))

# Clue 10: The person who likes milk is not in the fifth house.
solver.add(drink_vars[5] != drink_map['milk'])

# Clue 11: The person who smokes Blue Master is the coffee drinker.
solver.add(cigar_vars[house] == cigar_map['blue master'] for house in houses if drink_vars[house] == drink_map['coffee'])
solver.add(drink_vars[house] == drink_map['coffee'] for house in houses if cigar_vars[house] == cigar_map['blue master'])

# Clue 12: There is one house between the tea drinker and the coffee drinker.
solver.add(Or([And(drink_vars[i] == drink_map['tea'], drink_vars[j] == drink_map['coffee']) for i in range(1, 5) for j in range(1, 6) if abs(i-j) == 2]))

# Clue 13: Eric is in the third house.
solver.add(name_vars[3] == name_map['Eric'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        birthday = birthdays[model[birthday_vars[house]].as_long()]
        cigar = cigars[model[cigar_vars[house]].as_long()]
        drink = drinks[model[drink_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, birthday, cigar, drink])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")