from z3 import *

def main():
    # Define enums for attributes
    NameSort = Datatype('NameSort')
    for n in ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']:
        NameSort.declare(n)
    NameSort = NameSort.create()

    BirthdaySort = Datatype('BirthdaySort')
    for b in ['april', 'feb', 'mar', 'jan', 'sept']:
        BirthdaySort.declare(b)
    BirthdaySort = BirthdaySort.create()

    CigarSort = Datatype('CigarSort')
    for c in ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']:
        CigarSort.declare(c)
    CigarSort = CigarSort.create()

    DrinkSort = Datatype('DrinkSort')
    for d in ['water', 'coffee', 'tea', 'milk', 'root beer']:
        DrinkSort.declare(d)
    DrinkSort = DrinkSort.create()

    # Create variables for each house
    names = [Const(f'name_{i}', NameSort) for i in range(1, 6)]
    birthdays = [Const(f'birthday_{i}', BirthdaySort) for i in range(1, 6)]
    cigars = [Const(f'cigar_{i}', CigarSort) for i in range(1, 6)]
    drinks = [Const(f'drink_{i}', DrinkSort) for i in range(1, 6)]

    s = Solver()

    # All attributes must have unique values
    s.add(Distinct(names))
    s.add(Distinct(birthdays))
    s.add(Distinct(cigars))
    s.add(Distinct(drinks))

    # Clue 1: The root beer lover is Eric.
    s.add(Or([And(names[i] == NameSort.Eric, drinks[i] == DrinkSort.root_beer) for i in range(5)]))

    # Clue 2: Pall Mall is in the third house.
    s.add(cigars[2] == CigarSort.pall_mall)

    # Clue 3: April birthday is Bob.
    s.add(Or([And(names[i] == NameSort.Bob, birthdays[i] == BirthdaySort.april) for i in range(5)]))

    # Clue 4: Dunhill smoker has March birthday.
    s.add(Or([And(cigars[i] == CigarSort.dunhill, birthdays[i] == BirthdaySort.mar) for i in range(5)]))

    # Clue 5: Peter is to the right of root beer lover (Eric in house 3, so root beer in house 3).
    # Since Eric is in house 3 (from clue 13) and root beer is Eric, so root beer in house 3.
    # Peter must be in house 4 or 5.
    s.add(Or([And(names[i] == NameSort.Peter) for i in [3, 4]]))  # indices 3 and 4 are houses 4 and 5 (0-indexed)
    for i in range(5):
        if i < 2:  # Peter must be right of house 3 (index 2), so only indices 3 and 4 (houses 4 and 5)
            s.add(names[i] != NameSort.Peter)

    # Clue 6: One house between January birthday and Peter.
    # |house(jan) - house(Peter)| = 2
    jan_index = Const('jan_index', IntSort())
    peter_index = Const('peter_index', IntSort())
    s.add(Or([And(birthdays[i] == BirthdaySort.jan, jan_index == i) for i in range(5)]))
    s.add(Or([And(names[i] == NameSort.Peter, peter_index == i) for i in range(5)]))
    s.add(Abs(jan_index - peter_index) == 2)

    # Clue 7: Blends smoker has February birthday.
    s.add(Or([And(cigars[i] == CigarSort.blends, birthdays[i] == BirthdaySort.feb) for i in range(5)]))

    # Clue 8: February birthday is in the second house.
    s.add(birthdays[1] == BirthdaySort.feb)  # house 2 is index 1

    # Clue 9: Arnold is directly left of Peter.
    arnold_index = Const('arnold_index', IntSort())
    s.add(Or([And(names[i] == NameSort.Arnold, arnold_index == i) for i in range(5)]))
    s.add(arnold_index + 1 == peter_index)

    # Clue 10: Milk drinker is not in the fifth house.
    s.add(drinks[4] != DrinkSort.milk)

    # Clue 11: Blue Master smoker is coffee drinker.
    s.add(Or([And(cigars[i] == CigarSort.blue_master, drinks[i] == DrinkSort.coffee) for i in range(5)]))

    # Clue 12: One house between tea drinker and coffee drinker.
    tea_index = Const('tea_index', IntSort())
    coffee_index = Const('coffee_index', IntSort())
    s.add(Or([And(drinks[i] == DrinkSort.tea, tea_index == i) for i in range(5)]))
    s.add(Or([And(drinks[i] == DrinkSort.coffee, coffee_index == i) for i in range(5)]))
    s.add(Abs(tea_index - coffee_index) == 2)

    # Clue 13: Eric is in the third house.
    s.add(names[2] == NameSort.Eric)

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        solution = []
        for i in range(5):
            name_val = m.eval(names[i])
            birthday_val = m.eval(birthdays[i])
            cigar_val = m.eval(cigars[i])
            drink_val = m.eval(drinks[i])
            solution.append((
                str(i+1),
                str(name_val),
                str(birthday_val),
                str(cigar_val),
                str(drink_val)
            ))
        
        # Format the solution as JSON
        json_output = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                "rows": solution
            }
        }
        import json
        print(json.dumps(json_output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()