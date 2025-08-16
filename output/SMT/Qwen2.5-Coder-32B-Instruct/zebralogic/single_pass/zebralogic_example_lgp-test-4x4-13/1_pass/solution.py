from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each attribute
houses = [1, 2, 3, 4]
names = ['Alice', 'Peter', 'Arnold', 'Eric']
cigars = ['prince', 'dunhill', 'blue master', 'pall mall']
sports = ['swimming', 'basketball', 'soccer', 'tennis']
drinks = ['coffee', 'water', 'milk', 'tea']

# Declare variables
name_vars = {house: Int(f'name_{house}') for house in houses}
cigar_vars = {house: Int(f'cigar_{house}') for house in houses}
sport_vars = {house: Int(f'sport_{house}') for house in houses}
drink_vars = {house: Int(f'drink_{house}') for house in houses}

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([cigar_vars[house] for house in houses]))
solver.add(Distinct([sport_vars[house] for house in houses]))
solver.add(Distinct([drink_vars[house] for house in houses]))

# Map indices to actual values
name_map = {i: names[i] for i in range(len(names))}
cigar_map = {i: cigars[i] for i in range(len(cigars))}
sport_map = {i: sports[i] for i in range(len(sports))}
drink_map = {i: drinks[i] for i in range(len(drinks))}

# Clue 1: Peter is in the fourth house.
solver.add(name_vars[4] == names.index('Peter'))

# Clue 2: The tea drinker is the person who loves basketball.
solver.add(And(drink_vars[h] == drinks.index('tea'), sport_vars[h] == sports.index('basketball')) for h in houses)

# Clue 3: Arnold is the person who smokes Blue Master.
solver.add(And(name_vars[h] == names.index('Arnold'), cigar_vars[h] == cigars.index('blue master')) for h in houses)

# Clue 4: The person who loves basketball is Eric.
solver.add(And(sport_vars[h] == sports.index('basketball'), name_vars[h] == names.index('Eric')) for h in houses)

# Clue 5: The person who loves tennis is the person who smokes Blue Master.
solver.add(And(sport_vars[h] == sports.index('tennis'), cigar_vars[h] == cigars.index('blue master')) for h in houses)

# Clue 6: There are two houses between the one who only drinks water and Peter.
solver.add(Abs(drink_vars[h] - drinks.index('water')) == 2 for h in houses if h != 4)

# Clue 7: The coffee drinker is Arnold.
solver.add(And(drink_vars[h] == drinks.index('coffee'), name_vars[h] == names.index('Arnold')) for h in houses)

# Clue 8: The person who loves basketball is in the third house.
solver.add(sport_vars[3] == sports.index('basketball'))

# Clue 9: The Prince smoker is the person who loves soccer.
solver.add(And(cigar_vars[h] == cigars.index('prince'), sport_vars[h] == sports.index('soccer')) for h in houses)

# Clue 10: Peter is the person partial to Pall Mall.
solver.add(And(name_vars[h] == names.index('Peter'), cigar_vars[h] == cigars.index('pall mall')) for h in houses)

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = name_map[model.evaluate(name_vars[house]).as_long()]
        cigar = cigar_map[model.evaluate(cigar_vars[house]).as_long()]
        sport = sport_map[model.evaluate(sport_vars[house]).as_long()]
        drink = drink_map[model.evaluate(drink_vars[house]).as_long()]
        solution.append([str(house), name, cigar, sport, drink])
    
    # Output the solution in the required format
    print({
        "solution": {
            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
            "rows": solution
        }
    })
else:
    print("No solution found")