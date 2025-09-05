import json
from z3 import *

def main():
    # Create the solver
    solver = Solver()

    # Define the attributes and their possible values
    names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
    birthdays = ['april', 'feb', 'mar', 'jan', 'sept']
    cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
    drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']

    # Create enumeration sorts for each attribute
    NameSort, (Peter, Alice, Eric, Bob, Arnold) = EnumSort('Name', names)
    BirthdaySort, (april, feb, mar, jan, sept) = EnumSort('Birthday', birthdays)
    CigarSort, (pall_mall, prince, dunhill, blends, blue_master) = EnumSort('Cigar', cigars)
    DrinkSort, (water, coffee, tea, milk, root_beer) = EnumSort('Drink', drinks)

    # Create variables for each house for each attribute
    house_names = [Const(f'name_{i}', NameSort) for i in range(1, 6)]
    house_birthdays = [Const(f'birthday_{i}', BirthdaySort) for i in range(1, 6)]
    house_cigars = [Const(f'cigar_{i}', CigarSort) for i in range(1, 6)]
    house_drinks = [Const(f'drink_{i}', DrinkSort) for i in range(1, 6)]

    # Add constraints that all attributes are unique
    solver.add(Distinct(house_names))
    solver.add(Distinct(house_birthdays))
    solver.add(Distinct(house_cigars))
    solver.add(Distinct(house_drinks))

    # Clue 1: The root beer lover is Eric.
    for i in range(5):
        solver.add(Implies(house_drinks[i] == root_beer, house_names[i] == Eric))

    # Clue 2: The person partial to Pall Mall is in the third house.
    solver.add(house_cigars[2] == pall_mall)

    # Clue 3: The person whose birthday is in April is Bob.
    for i in range(5):
        solver.add(Implies(house_birthdays[i] == april, house_names[i] == Bob))

    # Clue 4: The Dunhill smoker is the person whose birthday is in March.
    for i in range(5):
        solver.add(Implies(house_cigars[i] == dunhill, house_birthdays[i] == mar))

    # Clue 5: Peter is somewhere to the right of the root beer lover.
    root_beer_house = Int('root_beer_house')
    solver.add(root_beer_house >= 1, root_beer_house <= 5)
    for i in range(5):
        solver.add(If(house_drinks[i] == root_beer, root_beer_house == i+1, True))
    peter_house = Int('peter_house')
    solver.add(peter_house >= 1, peter_house <= 5)
    for i in range(5):
        solver.add(If(house_names[i] == Peter, peter_house == i+1, True))
    solver.add(peter_house > root_beer_house)

    # Clue 6: There is one house between the person whose birthday is in January and Peter.
    jan_house = Int('jan_house')
    solver.add(jan_house >= 1, jan_house <= 5)
    for i in range(5):
        solver.add(If(house_birthdays[i] == jan, jan_house == i+1, True))
    solver.add(Or(jan_house + 2 == peter_house, jan_house - 2 == peter_house))

    # Clue 7: The person who smokes blends is the person whose birthday is in February.
    for i in range(5):
        solver.add(Implies(house_cigars[i] == blends, house_birthdays[i] == feb))

    # Clue 8: The person whose birthday is in February is in the second house.
    solver.add(house_birthdays[1] == feb)

    # Clue 9: Arnold is directly left of Peter.
    arnold_house = Int('arnold_house')
    solver.add(arnold_house >= 1, arnold_house <= 5)
    for i in range(5):
        solver.add(If(house_names[i] == Arnold, arnold_house == i+1, True))
    solver.add(arnold_house + 1 == peter_house)

    # Clue 10: The person who likes milk is not in the fifth house.
    solver.add(house_drinks[4] != milk)

    # Clue 11: The person who smokes Blue Master is the coffee drinker.
    for i in range(5):
        solver.add(Implies(house_cigars[i] == blue_master, house_drinks[i] == coffee))

    # Clue 12: There is one house between the tea drinker and the coffee drinker.
    tea_house = Int('tea_house')
    coffee_house = Int('coffee_house')
    solver.add(tea_house >= 1, tea_house <= 5)
    solver.add(coffee_house >= 1, coffee_house <= 5)
    for i in range(5):
        solver.add(If(house_drinks[i] == tea, tea_house == i+1, True))
        solver.add(If(house_drinks[i] == coffee, coffee_house == i+1, True))
    solver.add(Or(tea_house + 2 == coffee_house, tea_house - 2 == coffee_house))

    # Clue 13: Eric is in the third house.
    solver.add(house_names[2] == Eric)

    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare the result table
        header = ["House", "Name", "Birthday", "Cigar", "Drink"]
        rows = []
        
        # Map the model values back to the original strings
        name_map = {Peter: 'Peter', Alice: 'Alice', Eric: 'Eric', Bob: 'Bob', Arnold: 'Arnold'}
        birthday_map = {april: 'april', feb: 'feb', mar: 'mar', jan: 'jan', sept: 'sept'}
        cigar_map = {pall_mall: 'pall mall', prince: 'prince', dunhill: 'dunhill', blends: 'blends', blue_master: 'blue master'}
        drink_map = {water: 'water', coffee: 'coffee', tea: 'tea', milk: 'milk', root_beer: 'root beer'}
        
        for i in range(5):
            house_num = str(i+1)
            name_val = model.eval(house_names[i])
            birthday_val = model.eval(house_birthdays[i])
            cigar_val = model.eval(house_cigars[i])
            drink_val = model.eval(house_drinks[i])
            
            rows.append([
                house_num,
                name_map[name_val],
                birthday_map[birthday_val],
                cigar_map[cigar_val],
                drink_map[drink_val]
            ])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()