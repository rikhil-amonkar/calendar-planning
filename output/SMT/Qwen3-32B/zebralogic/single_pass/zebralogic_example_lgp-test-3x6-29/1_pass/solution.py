from z3 import *

def solve():
    # Define EnumSorts
    Names, (Arnold, Peter, Eric) = EnumSort('Names', ['Arnold', 'Peter', 'Eric'])
    Animals, (bird, horse, cat) = EnumSort('Animals', ['bird', 'horse', 'cat'])
    Birthday, (jan, sept, april) = EnumSort('Birthday', ['jan', 'sept', 'april'])
    Hobby, (photography, cooking, gardening) = EnumSort('Hobby', ['photography', 'cooking', 'gardening'])
    Drink, (milk, water, tea) = EnumSort('Drink', ['milk', 'water', 'tea'])
    HairColor, (black, brown, blonde) = EnumSort('HairColor', ['black', 'brown', 'blonde'])

    # Create variables for each house (0,1,2 for houses 1,2,3)
    name = [Const(f'name_{i}', Names) for i in range(3)]
    animal = [Const(f'animal_{i}', Animals) for i in range(3)]
    birthday = [Const(f'birthday_{i}', Birthday) for i in range(3)]
    hobby = [Const(f'hobby_{i}', Hobby) for i in range(3)]
    drink = [Const(f'drink_{i}', Drink) for i in range(3)]
    haircolor = [Const(f'haircolor_{i}', HairColor) for i in range(3)]

    solver = Solver()

    # Add uniqueness constraints
    for lst in [name, animal, birthday, hobby, drink, haircolor]:
        solver.add(Distinct(lst))

    # Add clues
    # Clue 2: April in house 3 (index 2)
    solver.add(birthday[2] == april)

    # Clue 3: Eric not in first house (index 0)
    solver.add(name[0] != Eric)

    # Clue 4: Cat in house 2 (index 1)
    solver.add(animal[1] == cat)

    # Clue 7: Cat lover has brown hair (house 2, index 1)
    solver.add(haircolor[1] == brown)

    # Clue 1: Brown hair implies cooking hobby
    for i in range(3):
        solver.add(If(haircolor[i] == brown, hobby[i] == cooking, True))

    # Clue 6: Gardening implies milk
    for i in range(3):
        solver.add(Implies(hobby[i] == gardening, drink[i] == milk))

    # Clue 8: Arnold has bird
    for i in range(3):
        solver.add(If(name[i] == Arnold, animal[i] == bird, True))

    # Clue 9: Water implies photography
    for i in range(3):
        solver.add(Implies(drink[i] == water, hobby[i] == photography))

    # Clue 5: Blonde left of milk
    solver.add(Or(
        And(haircolor[0] == blonde, Or(drink[1] == milk, drink[2] == milk)),
        And(haircolor[1] == blonde, drink[2] == milk),
        haircolor[2] != blonde
    ))

    # Clue 10: Sept birthday directly left of Arnold
    solver.add(Or(
        And(birthday[0] == sept, name[1] == Arnold),
        And(birthday[1] == sept, name[2] == Arnold)
    ))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        # Extract the values for each house
        solution = []
        for i in range(3):
            house_num = str(i + 1)
            n = model[name[i]].__name__
            a = model[animal[i]].__name__
            b = model[birthday[i]].__name__
            h = model[hobby[i]].__name__
            d = model[drink[i]].__name__
            hc = model[haircolor[i]].__name__
            solution.append([house_num, n, a, b, h, d, hc])
        # Return the JSON structure
        import json
        print(json.dumps({
            "solution": {
                "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                "rows": solution
            }
        }))
    else:
        print("No solution found")

solve()