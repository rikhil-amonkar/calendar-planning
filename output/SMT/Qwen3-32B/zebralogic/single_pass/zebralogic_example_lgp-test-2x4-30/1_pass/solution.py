import json
from z3 import *

def solve_puzzle():
    # Define EnumSorts
    Name, (arnold, eric) = EnumSort('Name', ['Arnold', 'Eric'])
    HairColor, (black, brown) = EnumSort('HairColor', ['black', 'brown'])
    Sport, (basketball, soccer) = EnumSort('Sport', ['basketball', 'soccer'])
    Smoothie, (desert, cherry) = EnumSort('Smoothie', ['desert', 'cherry'])

    # Variables for house 1 and 2
    n1 = Const('n1', Name)
    h1 = Const('h1', HairColor)
    s1 = Const('s1', Sport)
    sm1 = Const('sm1', Smoothie)

    n2 = Const('n2', Name)
    h2 = Const('h2', HairColor)
    s2 = Const('s2', Sport)
    sm2 = Const('sm2', Smoothie)

    solver = Solver()

    # Uniqueness constraints
    solver.add(Distinct(n1, n2))
    solver.add(Distinct(h1, h2))
    solver.add(Distinct(s1, s2))
    solver.add(Distinct(sm1, sm2))

    # Clue 1: Desert lover is Arnold
    solver.add(Implies(sm1 == desert, n1 == arnold))
    solver.add(Implies(sm2 == desert, n2 == arnold))

    # Clue 2: Brown hair loves basketball
    solver.add(Implies(h1 == brown, s1 == basketball))
    solver.add(Implies(h2 == brown, s2 == basketball))

    # Clue 3: Arnold is left of black hair
    arnold_house = If(n1 == arnold, 1, 2)
    black_house = If(h1 == black, 1, 2)
    solver.add(arnold_house < black_house)

    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        # Extract values for house 1 and 2
        # House 1
        name1 = model[n1].decl().name()
        hair1 = model[h1].decl().name()
        sport1 = model[s1].decl().name()
        smoothie1 = model[sm1].decl().name()

        # House 2
        name2 = model[n2].decl().name()
        hair2 = model[h2].decl().name()
        sport2 = model[s2].decl().name()
        smoothie2 = model[sm2].decl().name()

        # Create the JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                "rows": [
                    ["1", name1, hair1, sport1, smoothie1],
                    ["2", name2, hair2, sport2, smoothie2]
                ]
            }
        }
        return solution
    else:
        return None

# Generate and print the JSON solution
solution = solve_puzzle()
print(json.dumps(solution))