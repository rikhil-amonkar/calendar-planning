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
        solver.add(Or([house_names[i] == name for name in names]))
        solver.add(Or([house_birthdays[i] == bday for bday in birthdays]))
        solver.add(Or([house_cigars[i] == cigar for cigar in cigars]))
        solver.add(Or([house_drinks[i] == drink for drink in drinks]))

    # All attributes must be unique
    solver.add(Distinct(house_names))
    solver.add(Distinct(house_birthdays))
    solver.add(Distinct(house_cigars))
    solver.add(Distinct(house_drinks))

    # Add the clues
    # Clue 1: The root beer lover is Eric.
    root_beer_house = Int('root_beer_house')
    solver.add(Or([And(house_drinks[i] == 'root beer', root_beer_house == i) for i in range(5)]))

    # Clue 2: The person partial to Pall Mall is in the third house.
    solver.add(house_cigars[2] == 'pall mall')

    # Clue 3: The person whose birthday is in April is Bob.
    april_house = Int('april_house')
    solver.add(Or([And(house_birthdays[i] == 'april', april_house == i) for i in range(5)]))
    solver.add(house_names[april_house] == 'Bob')

    # Clue 4: The Dunhill smoker is the person whose birthday is in March.
    dunhill_house = Int('dunhill_house')
    solver.add(Or([And(house_cigars[i] == 'dunhill', dunhill_house == i) for i in range(5)]))
    solver.add(house_birthdays[dunhill_house] == 'mar')

    # Clue 5: Peter is somewhere to the right of the root beer lover.
    peter_house = Int('peter_house')
    solver.add(Or([And(house_names[i] == 'Peter', peter_house == i) for i in range(5)]))
    solver.add(peter_house > root_beer_house)

    # Clue 6: There is one house between the person whose birthday is in January and Peter.
    jan_house = Int('jan_house')
    solver.add(Or([And(house_birthdays[i] == 'jan', jan_house == i) for i in range(5)]))
    solver.add(Or(jan_house == peter_house - 2, jan_house == peter_house + 2))

    # Clue 7: The person who smokes many unique blends is the person whose birthday is in February.
    blends_house = Int('blends_house')
    solver.add(Or([And(house_cigars[i] == 'blends', blends_house == i) for i in range(5)]))
    solver.add(house_birthdays[blends_house] == 'feb')

    # Clue 8: The person whose birthday is in February is in the second house.
    solver.add(house_birthdays[1] == 'feb')

    # Clue 9: Arnold is directly left of Peter.
    arnold_house = Int('arnold_house')
    solver.add(Or([And(house_names[i] == 'Arnold', arnold_house == i) for i in range(5)]))
    solver.add(arnold_house == peter_house - 1)

    # Clue 10: The person who likes milk is not in the fifth house.
    solver.add(house_drinks[4] != 'milk')

    # Clue 11: The person who smokes Blue Master is the coffee drinker.
    blue_master_house = Int('blue_master_house')
    solver.add(Or([And(house_cigars[i] == 'blue master', blue_master_house == i) for i in range(5)]))
    solver.add(house_drinks[blue_master_house] == 'coffee')

    # Clue 12: There is one house between the tea drinker and the coffee drinker.
    tea_house = Int('tea_house')
    coffee_house = Int('coffee_house')
    solver.add(Or([And(house_drinks[i] == 'tea', tea_house == i) for i in range(5)]))
    solver.add(Or([And(house_drinks[i] == 'coffee', coffee_house == i) for i in range(5)]))
    solver.add(Or(tea_house == coffee_house - 2, tea_house == coffee_house + 2))

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

        # Ensure the root beer lover is Eric
        root_beer_house_value = model.evaluate(root_beer_house).as_long()
        assert model[house_names[root_beer_house_value]].as_string()[1:-1] == 'Eric'

        return {
            "solution": {
                "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                "rows": solution
            }
        }

# Print the solution in JSON format
import json
print(json.dumps(solve_puzzle(), indent=2))