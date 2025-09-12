import json
from z3 import *

def solve_puzzle():
    # Define EnumSorts
    Name, (Bob, Arnold, Peter, Alice, Eric) = EnumSort('Name', ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric'])
    Drink, (milk, root_beer, coffee, tea, water) = EnumSort('Drink', ['milk', 'root beer', 'coffee', 'tea', 'water'])
    Color, (blue, green, white, yellow, red) = EnumSort('Color', ['blue', 'green', 'white', 'yellow', 'red'])
    Flower, (daffodils, roses, lilies, tulips, carnations) = EnumSort('Flower', ['daffodils', 'roses', 'lilies', 'tulips', 'carnations'])
    Hobby, (painting, cooking, photography, gardening, knitting) = EnumSort('Hobby', ['painting', 'cooking', 'photography', 'gardening', 'knitting'])

    houses = 5
    name = [Const(f'name_{i}', Name) for i in range(houses)]
    drink = [Const(f'drink_{i}', Drink) for i in range(houses)]
    color = [Const(f'color_{i}', Color) for i in range(houses)]
    flower = [Const(f'flower_{i}', Flower) for i in range(houses)]
    hobby = [Const(f'hobby_{i}', Hobby) for i in range(houses)]

    s = Solver()

    # Add distinct constraints
    s.add(Distinct(name))
    s.add(Distinct(drink))
    s.add(Distinct(color))
    s.add(Distinct(flower))
    s.add(Distinct(hobby))

    # Clue 1: Alice is not in the fourth house (index 3)
    s.add(name[3] != Alice)

    # Clue 2: root beer lover is gardening
    for i in range(houses):
        s.add(Implies(drink[i] == root_beer, hobby[i] == gardening))

    # Clue 3: green color implies coffee
    for i in range(houses):
        s.add(Implies(color[i] == green, drink[i] == coffee))

    # Clue 4: green color implies lilies
    for i in range(houses):
        s.add(Implies(color[i] == green, flower[i] == lilies))

    # Clue 5: blue is to the right of daffodils
    daffodils_pos = Int('daffodils_pos')
    blue_pos = Int('blue_pos')
    s.add(And(0 <= daffodils_pos, daffodils_pos <= 4))
    s.add(And(0 <= blue_pos, blue_pos <= 4))
    for i in range(houses):
        s.add(Implies(daffodils_pos == i, flower[i] == daffodils))
        s.add(Implies(daffodils_pos != i, flower[i] != daffodils))
        s.add(Implies(blue_pos == i, color[i] == blue))
        s.add(Implies(blue_pos != i, color[i] != blue))
    s.add(blue_pos > daffodils_pos)

    # Clue 6: cooking is blue
    cooking_pos = Int('cooking_pos')
    s.add(And(0 <= cooking_pos, cooking_pos <= 4))
    for i in range(houses):
        s.add(Implies(cooking_pos == i, hobby[i] == cooking))
        s.add(Implies(cooking_pos != i, hobby[i] != cooking))
    s.add(cooking_pos == blue_pos)

    # Clue 7: Eric is directly left of tea
    eric_pos = Int('eric_pos')
    s.add(And(0 <= eric_pos, eric_pos <= 3))
    for i in range(houses):
        s.add(Implies(eric_pos == i, name[i] == Eric))
        s.add(Implies(eric_pos != i, name[i] != Eric))
    s.add(drink[eric_pos + 1] == tea)

    # Clue 8: Peter is water drinker
    peter_pos = Int('peter_pos')
    s.add(And(0 <= peter_pos, peter_pos <= 4))
    for i in range(houses):
        s.add(Implies(peter_pos == i, name[i] == Peter))
        s.add(Implies(peter_pos != i, name[i] != Peter))
    s.add(drink[peter_pos] == water)

    # Clue 9: Arnold is photography
    arnold_pos = Int('arnold_pos')
    s.add(And(0 <= arnold_pos, arnold_pos <= 4))
    for i in range(houses):
        s.add(Implies(arnold_pos == i, name[i] == Arnold))
        s.add(Implies(arnold_pos != i, name[i] != Arnold))
    s.add(hobby[arnold_pos] == photography)

    # Clue 10: white implies roses
    white_pos = Int('white_pos')
    s.add(And(0 <= white_pos, white_pos <= 4))
    for i in range(houses):
        s.add(Implies(white_pos == i, color[i] == white))
        s.add(Implies(white_pos != i, color[i] != white))
    s.add(flower[white_pos] == roses)

    # Clue 13: water is in third house (index 2)
    s.add(peter_pos == 2)

    # Clue 15: white is in second house (index 1)
    s.add(white_pos == 1)

    # Clue 14: carnations implies root beer
    carnations_pos = Int('carnations_pos')
    s.add(And(0 <= carnations_pos, carnations_pos <= 4))
    for i in range(houses):
        s.add(Implies(carnations_pos == i, flower[i] == carnations))
        s.add(Implies(carnations_pos != i, flower[i] != carnations))
    s.add(drink[carnations_pos] == root_beer)

    # Clue 11: one house between carnations and red
    red_pos = Int('red_pos')
    s.add(And(0 <= red_pos, red_pos <= 4))
    for i in range(houses):
        s.add(Implies(red_pos == i, color[i] == red))
        s.add(Implies(red_pos != i, color[i] != red))
    s.add(Or(carnations_pos == red_pos - 2, carnations_pos == red_pos + 2))

    # Clue 12: cooking is left of painting
    painting_pos = Int('painting_pos')
    s.add(And(0 <= painting_pos, painting_pos <= 4))
    for i in range(houses):
        s.add(Implies(painting_pos == i, hobby[i] == painting))
        s.add(Implies(painting_pos != i, hobby[i] != painting))
    s.add(cooking_pos < painting_pos)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the solution
        solution = []
        for i in range(houses):
            house_num = i + 1
            name_val = model[name[i]].decl().name()
            drink_val = model[drink[i]].decl().name()
            color_val = model[color[i]].decl().name()
            flower_val = model[flower[i]].decl().name()
            hobby_val = model[hobby[i]].decl().name()
            solution.append([str(house_num), name_val, drink_val, color_val, flower_val, hobby_val])
        return {
            "solution": {
                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                "rows": solution
            }
        }
    else:
        return None

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))