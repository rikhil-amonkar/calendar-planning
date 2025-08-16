from z3 import *

def solve_puzzle():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5]

    # Define the attributes
    names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
    months = ['april', 'feb', 'mar', 'jan', 'sept']
    cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
    drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']

    # Create variables for each attribute in each house
    name = {h: String(f'name_{h}') for h in houses}
    month = {h: String(f'month_{h}') for h in houses}
    cigar = {h: String(f'cigar_{h}') for h in houses}
    drink = {h: String(f'drink_{h}') for h in houses}

    # Add constraints that all attributes are unique within their category
    s.add(Distinct([name[h] for h in houses]))
    s.add(Distinct([month[h] for h in houses]))
    s.add(Distinct([cigar[h] for h in houses]))
    s.add(Distinct([drink[h] for h in houses]))

    # Each attribute must be one of the allowed values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([month[h] == m for m in months]))
        s.add(Or([cigar[h] == c for c in cigars]))
        s.add(Or([drink[h] == d for d in drinks]))

    # Clue 1: The root beer lover is Eric.
    for h in houses:
        s.add(Implies(drink[h] == 'root beer', name[h] == 'Eric'))

    # Clue 2: The person partial to Pall Mall is in the third house.
    s.add(cigar[3] == 'pall mall')

    # Clue 3: The person whose birthday is in April is Bob.
    for h in houses:
        s.add(Implies(month[h] == 'april', name[h] == 'Bob'))

    # Clue 4: The Dunhill smoker is the person whose birthday is in March.
    for h in houses:
        s.add(Implies(cigar[h] == 'dunhill', month[h] == 'mar'))

    # Clue 5: Peter is somewhere to the right of the root beer lover.
    # Find the house where drink is root beer, then Peter must be in a higher-numbered house.
    root_beer_house = Int('root_beer_house')
    s.add(And(root_beer_house >= 1, root_beer_house <= 5))
    for h in houses:
        s.add(Implies(drink[h] == 'root beer', root_beer_house == h))
    peter_house = Int('peter_house')
    s.add(And(peter_house >= 1, peter_house <= 5))
    for h in houses:
        s.add(Implies(name[h] == 'Peter', peter_house == h))
    s.add(peter_house > root_beer_house)

    # Clue 6: There is one house between the person whose birthday is in January and Peter.
    jan_house = Int('jan_house')
    s.add(And(jan_house >= 1, jan_house <= 5))
    for h in houses:
        s.add(Implies(month[h] == 'jan', jan_house == h))
    s.add(Or(
        And(jan_house == 1, peter_house == 3),
        And(jan_house == 2, peter_house == 4),
        And(jan_house == 3, peter_house == 5)
    ))

    # Clue 7: The person who smokes blends is the person whose birthday is in February.
    for h in houses:
        s.add(Implies(cigar[h] == 'blends', month[h] == 'feb'))

    # Clue 8: The person whose birthday is in February is in the second house.
    s.add(month[2] == 'feb')

    # Clue 9: Arnold is directly left of Peter.
    # This means Arnold is in house peter_house - 1
    s.add(And(peter_house > 1, peter_house <= 5))
    s.add(name[peter_house - 1] == 'Arnold')

    # Clue 10: The person who likes milk is not in the fifth house.
    for h in houses:
        if h == 5:
            s.add(drink[h] != 'milk')

    # Clue 11: The person who smokes Blue Master is the coffee drinker.
    for h in houses:
        s.add(Implies(cigar[h] == 'blue master', drink[h] == 'coffee'))

    # Clue 12: There is one house between the tea drinker and the coffee drinker.
    # This means if tea is in house X, coffee is in X+2, or vice versa.
    tea_house = Int('tea_house')
    coffee_house = Int('coffee_house')
    s.add(And(tea_house >= 1, tea_house <= 5))
    s.add(And(coffee_house >= 1, coffee_house <= 5))
    for h in houses:
        s.add(Implies(drink[h] == 'tea', tea_house == h))
        s.add(Implies(drink[h] == 'coffee', coffee_house == h))
    s.add(Or(
        And(tea_house + 2 == coffee_house),
        And(coffee_house + 2 == tea_house)
    ))

    # Clue 13: Eric is in the third house.
    s.add(name[3] == 'Eric')

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                "rows": []
            }
        }
        for h in houses:
            row = [
                str(h),
                m.evaluate(name[h]).as_string(),
                m.evaluate(month[h]).as_string(),
                m.evaluate(cigar[h]).as_string(),
                m.evaluate(drink[h]).as_string()
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"solution": {"header": [], "rows": []}}

# Print the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))