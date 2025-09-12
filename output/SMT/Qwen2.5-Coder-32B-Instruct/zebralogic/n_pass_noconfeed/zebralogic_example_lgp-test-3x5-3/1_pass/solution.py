from z3 import *

def solve_puzzle():
    # Create Solver instance
    solver = Solver()

    # Define domains
    houses = [1, 2, 3]
    names = ['Eric', 'Peter', 'Arnold']
    smoothies = ['cherry', 'watermelon', 'desert']
    flowers = ['carnations', 'lilies', 'daffodils']
    animals = ['cat', 'horse', 'bird']
    hobbies = ['photography', 'cooking', 'gardening']

    # Create variables
    house_of = {}
    for attr in [names, smoothies, flowers, animals, hobbies]:
        for item in attr:
            house_of[item] = Int(f'house_of_{item}')

    # Add domain constraints
    for item in house_of.values():
        solver.add(And(item >= 1, item <= 3))

    # All items must be in different houses
    for attr in [names, smoothies, flowers, animals, hobbies]:
        solver.add(Distinct([house_of[item] for item in attr]))

    # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
    solver.add(Abs(house_of['horse'] - house_of['photography']) == 1)

    # Clue 2: The bird keeper is the person who likes Cherry smoothies.
    solver.add(house_of['bird'] == house_of['cherry'])

    # Clue 3: The person who loves cooking is the Desert smoothie lover.
    solver.add(house_of['cooking'] == house_of['desert'])

    # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
    solver.add(house_of['gardening'] == house_of['carnations'])

    # Clue 5: The person who loves cooking is directly left of Peter.
    solver.add(house_of['cooking'] + 1 == house_of['Peter'])

    # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
    solver.add(house_of['daffodils'] == house_of['desert'])

    # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
    solver.add(house_of['watermelon'] == house_of['horse'])

    # Clue 8: The photography enthusiast is Eric.
    solver.add(house_of['photography'] == house_of['Eric'])

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": []
            }
        }
        for house in houses:
            row = [str(house)]
            for attr, var in house_of.items():
                if model.evaluate(var) == house:
                    row.append(attr)
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))