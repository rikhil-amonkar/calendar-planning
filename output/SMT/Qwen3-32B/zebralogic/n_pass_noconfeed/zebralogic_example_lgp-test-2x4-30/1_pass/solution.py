import json
from z3 import *

def main():
    # Define EnumSorts
    Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    HairColor, (black, brown) = EnumSort('HairColor', ['black', 'brown'])
    FavoriteSport, (basketball, soccer) = EnumSort('FavoriteSport', ['basketball', 'soccer'])
    Smoothie, (desert, cherry) = EnumSort('Smoothie', ['desert', 'cherry'])

    # House variables
    name1 = Const('name1', Name)
    hair1 = Const('hair1', HairColor)
    sport1 = Const('sport1', FavoriteSport)
    smoothie1 = Const('smoothie1', Smoothie)

    name2 = Const('name2', Name)
    hair2 = Const('hair2', HairColor)
    sport2 = Const('sport2', FavoriteSport)
    smoothie2 = Const('smoothie2', Smoothie)

    solver = Solver()

    # Uniqueness constraints
    solver.add(name1 != name2)
    solver.add(hair1 != hair2)
    solver.add(sport1 != sport2)
    solver.add(smoothie1 != smoothie2)

    # Clue 1: Desert lover is Arnold
    solver.add(Implies(name1 == Arnold, smoothie1 == desert))
    solver.add(Implies(name2 == Arnold, smoothie2 == desert))

    # Clue 2: Brown hair implies basketball
    solver.add(Implies(hair1 == brown, sport1 == basketball))
    solver.add(Implies(hair2 == brown, sport2 == basketball))

    # Clue 3: Arnold is left of black hair
    arnold_pos = If(name1 == Arnold, 1, 2)
    black_pos = If(hair1 == black, 1, 2)
    solver.add(arnold_pos < black_pos)

    if solver.check() == sat:
        model = solver.model()
        # Extract values for house 1 and 2
        n1 = model[name1].name()
        h1 = model[hair1].name()
        s1 = model[sport1].name()
        sm1 = model[smoothie1].name()

        n2 = model[name2].name()
        h2 = model[hair2].name()
        s2 = model[sport2].name()
        sm2 = model[smoothie2].name()

        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                "rows": [
                    ["1", n1, h1, s1, sm1],
                    ["2", n2, h2, s2, sm2]
                ]
            }
        }

        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()