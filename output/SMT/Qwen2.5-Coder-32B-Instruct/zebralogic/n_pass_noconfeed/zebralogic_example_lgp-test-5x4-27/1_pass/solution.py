from z3 import *

def solve_puzzle():
    # Define the variables
    names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
    birthdays = ['april', 'feb', 'mar', 'jan', 'sept']
    cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
    drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']

    # Create the solver
    solver = Solver()

    # Create arrays for each attribute
    house_names = [String(f'name_{i}') for i in range(1, 6)]
    house_birthdays = [String(f'bday_{i}') for i in range(1, 6)]
    house_cigars = [String(f'cigar_{i}') for i in range(1, 6)]
    house_drinks = [String(f'drink_{i}') for i in range(1, 6)]

    # Add domain constraints
    for i in range(5):
        solver.add(house_names[i] == Or([name for name in names]))
        solver.add(house_birthdays[i] == Or([bday for bday in birthdays]))
        solver.add(house_cigars[i] == Or([cigar for cigar in cigars]))
        solver.add(house_drinks[i] == Or([drink for drink in drinks]))

    # All attributes must be unique
    solver.add(Distinct(house_names))
    solver.add(Distinct(house_birthdays))
    solver.add(Distinct(house_cigars))
    solver.add(Distinct(house_drinks))

    # Add the clues
    # Clue 1: The root beer lover is Eric.
    solver.add(house_drinks.index('root beer') == house_names.index('Eric'))

    # Clue 2: The person partial to Pall Mall is in the third house.
    solver.add(house_cigars[2] == 'pall mall')

    # Clue 3: The person whose birthday is in April is Bob.
    solver.add(house_birthdays[3] == 'april')

    # Clue 4: The Dunhill smoker is the person whose birthday is in March.
    solver.add(house_cigars.index('dunhill') == house_birthdays.index('mar'))

    # Clue 5: Peter is somewhere to the right of the root beer lover.
    solver.add(house_names.index('Peter') > house_drinks.index('root beer'))

    # Clue 6: There is one house between the person whose birthday is in January and Peter.
    jan_index = house_birthdays.index('jan')
    peter_index = house_names.index('Peter')
    solver.add(Or(jan_index == peter_index - 2, jan_index == peter_index + 2))

    # Clue 7: The person who smokes many unique blends is the person whose birthday is in February.
    solver.add(house_cigars.index('blends') == house_birthdays.index('feb'))

    # Clue 8: The person whose birthday is in February is in the second house.
    solver.add(house_birthdays[1] == 'feb')

    # Clue 9: Arnold is directly left of Peter.
    solver.add(house_names.index('Arnold') == house_names.index('Peter') - 1)

    # Clue 10: The person who likes milk is not in the fifth house.
    solver.add(house_drinks[4] != 'milk')

    # Clue 11: The person who smokes Blue Master is the coffee drinker.
    solver.add(house_cigars.index('blue master') == house_drinks.index('coffee'))

    # Clue 12: There is one house between the tea drinker and the coffee drinker.
    tea_index = house_drinks.index('tea')
    coffee_index = house_drinks.index('coffee')
    solver.add(Or(tea_index == coffee_index - 2, tea_index == coffee_index + 2))

    # Clue 13: Eric is in the third house.
    solver.add(house_names[2] == 'Eric')

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for i in range(5):
            name = model[house_names[i]].as_string()[1:-1]
            birthday = model[house_birthdays[i]].as_string()[1:-1]
            cigar = model[house_cigars[i]].as_string()[1:-1]
            drink = model[house_drinks[i]].as_string()[1:-1]
            solution.append([str(i+1), name, birthday, cigar, drink])
        
        return {
            "solution": {
                "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                "rows": solution
            }
        }

# Print the solution in JSON format
import json
print(json.dumps(solve_puzzle(), indent=2))