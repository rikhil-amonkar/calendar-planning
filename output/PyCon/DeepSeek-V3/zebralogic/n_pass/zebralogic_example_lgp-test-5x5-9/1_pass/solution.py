import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    houses = [1, 2, 3, 4, 5]
    names = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
    drinks = ['milk', 'root beer', 'coffee', 'tea', 'water']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    flowers = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
    hobbies = ['painting', 'cooking', 'photography', 'gardening', 'knitting']
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'drink_{house}', drinks)
        problem.addVariable(f'color_{house}', colors)
        problem.addVariable(f'flower_{house}', flowers)
        problem.addVariable(f'hobby_{house}', hobbies)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), [f'name_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'drink_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'color_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'flower_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'hobby_{h}' for h in houses])
    
    # Clue 1: Alice is not in the fourth house.
    problem.addConstraint(lambda name: name != 'Alice', ['name_4'])
    
    # Clue 2: The root beer lover is the person who enjoys gardening.
    for house in houses:
        problem.addConstraint(
            lambda drink, hobby: not (drink == 'root beer') or (hobby == 'gardening'),
            [f'drink_{house}', f'hobby_{house}']
        )
        problem.addConstraint(
            lambda drink, hobby: not (hobby == 'gardening') or (drink == 'root beer'),
            [f'drink_{house}', f'hobby_{house}']
        )
    
    # Clue 3: The person whose favorite color is green is the coffee drinker.
    for house in houses:
        problem.addConstraint(
            lambda color, drink: not (color == 'green') or (drink == 'coffee'),
            [f'color_{house}', f'drink_{house}']
        )
        problem.addConstraint(
            lambda color, drink: not (drink == 'coffee') or (color == 'green'),
            [f'color_{house}', f'drink_{house}']
        )
    
    # Clue 4: The person whose favorite color is green is the person who loves the bouquet of lilies.
    for house in houses:
        problem.addConstraint(
            lambda color, flower: not (color == 'green') or (flower == 'lilies'),
            [f'color_{house}', f'flower_{house}']
        )
        problem.addConstraint(
            lambda color, flower: not (flower == 'lilies') or (color == 'green'),
            [f'color_{house}', f'flower_{house}']
        )
    
    # Clue 5: The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils.
    for h1 in houses:
        for h2 in houses:
            if h1 <= h2:
                problem.addConstraint(
                    lambda color1, flower2: not (color1 == 'blue' and flower2 == 'daffodils') or (h1 > h2),
                    [f'color_{h1}', f'flower_{h2}']
                )
    
    # Clue 6: The person who loves cooking is the person who loves blue.
    for house in houses:
        problem.addConstraint(
            lambda hobby, color: not (hobby == 'cooking') or (color == 'blue'),
            [f'hobby_{house}', f'color_{house}']
        )
        problem.addConstraint(
            lambda hobby, color: not (color == 'blue') or (hobby == 'cooking'),
            [f'hobby_{house}', f'color_{house}']
        )
    
    # Clue 7: Eric is directly left of the tea drinker.
    for h in range(1, 5):
        problem.addConstraint(
            lambda name, drink_next: (name == 'Eric') and (drink_next == 'tea'),
            [f'name_{h}', f'drink_{h+1}']
        )
    
    # Clue 8: The one who only drinks water is Peter.
    for house in houses:
        problem.addConstraint(
            lambda drink, name: not (drink == 'water') or (name == 'Peter'),
            [f'drink_{house}', f'name_{house}']
        )
        problem.addConstraint(
            lambda drink, name: not (name == 'Peter') or (drink == 'water'),
            [f'drink_{house}', f'name_{house}']
        )
    
    # Clue 9: Arnold is the photography enthusiast.
    for house in houses:
        problem.addConstraint(
            lambda name, hobby: not (name == 'Arnold') or (hobby == 'photography'),
            [f'name_{house}', f'hobby_{house}']
        )
        problem.addConstraint(
            lambda name, hobby: not (hobby == 'photography') or (name == 'Arnold'),
            [f'name_{house}', f'hobby_{house}']
        )
    
    # Clue 10: The person who loves white is the person who loves the rose bouquet.
    for house in houses:
        problem.addConstraint(
            lambda color, flower: not (color == 'white') or (flower == 'roses'),
            [f'color_{house}', f'flower_{house}']
        )
        problem.addConstraint(
            lambda color, flower: not (flower == 'roses') or (color == 'white'),
            [f'color_{house}', f'flower_{house}']
        )
    
    # Clue 11: There is one house between the person who loves a carnations arrangement and the person whose favorite color is red.
    for h1 in houses:
        for h2 in houses:
            if abs(h1 - h2) != 2:
                problem.addConstraint(
                    lambda flower, color: not (flower == 'carnations' and color == 'red'),
                    [f'flower_{h1}', f'color_{h2}']
                )
    
    # Clue 12: The person who loves cooking is somewhere to the left of the person who paints as a hobby.
    for h1 in houses:
        for h2 in houses:
            if h1 >= h2:
                problem.addConstraint(
                    lambda hobby1, hobby2: not (hobby1 == 'cooking' and hobby2 == 'painting'),
                    [f'hobby_{h1}', f'hobby_{h2}']
                )
    
    # Clue 13: The one who only drinks water is in the third house.
    problem.addConstraint(lambda drink: drink == 'water', ['drink_3'])
    
    # Clue 14: The person who loves a carnations arrangement is the root beer lover.
    for house in houses:
        problem.addConstraint(
            lambda flower, drink: not (flower == 'carnations') or (drink == 'root beer'),
            [f'flower_{house}', f'drink_{house}']
        )
        problem.addConstraint(
            lambda flower, drink: not (drink == 'root beer') or (flower == 'carnations'),
            [f'flower_{house}', f'drink_{house}']
        )
    
    # Clue 15: The person who loves white is in the second house.
    problem.addConstraint(lambda color: color == 'white', ['color_2'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the output
    header = ["House", "Name", "Drink", "Color", "Flower", "Hobby"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'drink_{house}'],
            solution[f'color_{house}'],
            solution[f'flower_{house}'],
            solution[f'hobby_{house}']
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))