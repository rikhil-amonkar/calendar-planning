from z3 import *

# Define variables
houses = [1, 2, 3, 4, 5]
names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
birthdays = ['april', 'feb', 'mar', 'jan', 'sept']
cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']

# Create dictionaries for each characteristic
name_vars = {house: Int(f'name_{house}') for house in houses}
birthday_vars = {house: Int(f'birthday_{house}') for house in houses}
cigar_vars = {house: Int(f'cigar_{house}') for house in houses}
drink_vars = {house: Int(f'drink_{house}') for house in houses}

# Create mappings for each characteristic to their respective indices
name_map = {name: i for i, name in enumerate(names)}
birthday_map = {birthday: i for i, birthday in enumerate(birthdays)}
cigar_map = {cigar: i for i, cigar in enumerate(cigars)}
drink_map = {drink: i for i, drink in enumerate(drinks)}

# Create solver
solver = Solver()

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([birthday_vars[house] for house in houses]))
solver.add(Distinct([cigar_vars[house] for house in houses]))
solver.add(Distinct([drink_vars[house] for house in houses]))

# Encode clues
# Clue 1: The root beer lover is Eric.
solver.add(drink_vars[name_map['Eric']] == drink_map['root beer'])

# Clue 2: The person partial to Pall Mall is in the third house.
solver.add(cigar_vars[3] == cigar_map['pall mall'])

# Clue 3: The person whose birthday is in April is Bob.
solver.add(birthday_vars[name_map['Bob']] == birthday_map['april'])

# Clue 4: The Dunhill smoker is the person whose birthday is in March.
solver.add(And(cigar_vars[birthday_map['mar']+1] == cigar_map['dunhill'], birthday_vars[birthday_map['mar']+1] == birthday_map['mar']))

# Clue 5: Peter is somewhere to the right of the root beer lover.
solver.add(name_vars[drink_map['root beer']+1] == name_map['Peter'])

# Clue 6: There is one house between the person whose birthday is in January and Peter.
solver.add(Or(Abs(birthday_vars[birthday_map['jan']+1] - name_vars[name_map['Peter']]) == 2))

# Clue 7: The person who smokes many unique blends is the person whose birthday is in February.
solver.add(And(cigar_vars[birthday_map['feb']+1] == cigar_map['blends'], birthday_vars[birthday_map['feb']+1] == birthday_map['feb']))

# Clue 8: The person whose birthday is in February is in the second house.
solver.add(birthday_vars[2] == birthday_map['feb'])

# Clue 9: Arnold is directly left of Peter.
solver.add(name_vars[name_map['Arnold']+1] == name_map['Peter'])

# Clue 10: The person who likes milk is not in the fifth house.
solver.add(drink_vars[5] != drink_map['milk'])

# Clue 11: The person who smokes Blue Master is the coffee drinker.
solver.add(And(cigar_vars[drink_map['coffee']+1] == cigar_map['blue master'], drink_vars[drink_map['coffee']+1] == drink_map['coffee']))

# Clue 12: There is one house between the tea drinker and the coffee drinker.
solver.add(Abs(drink_vars[drink_map['tea']+1] - drink_vars[drink_map['coffee']+1]) == 2)

# Clue 13: Eric is in the third house.
solver.add(name_vars[3] == name_map['Eric'])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the output
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": []
        }
    }
    
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        birthday = birthdays[model.evaluate(birthday_vars[house]).as_long()]
        cigar = cigars[model.evaluate(cigar_vars[house]).as_long()]
        drink = drinks[model.evaluate(drink_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, birthday, cigar, drink])
    
    print(solution)
else:
    print("No solution found")