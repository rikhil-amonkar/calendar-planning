from z3 import *

def main():
    # Define enums for each attribute
    Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    Sport, (basketball, soccer) = EnumSort('Sport', ['basketball', 'soccer'])
    Hair, (brown, black) = EnumSort('Hair', ['brown', 'black'])
    Height, (very_short, short) = EnumSort('Height', ['very short', 'short'])
    Smoothie, (desert, cherry) = EnumSort('Smoothie', ['desert', 'cherry'])
    Flower, (daffodils, carnations) = EnumSort('Flower', ['daffodils', 'carnations'])

    # Variables for house 1
    n1 = Const('n1', Name)
    s1 = Const('s1', Sport)
    hc1 = Const('hc1', Hair)
    ht1 = Const('ht1', Height)
    sm1 = Const('sm1', Smoothie)
    f1 = Const('f1', Flower)

    # Variables for house 2
    n2 = Const('n2', Name)
    s2 = Const('s2', Sport)
    hc2 = Const('hc2', Hair)
    ht2 = Const('ht2', Height)
    sm2 = Const('sm2', Smoothie)
    f2 = Const('f2', Flower)

    s = Solver()

    # All attributes must be unique per category
    s.add(Distinct(n1, n2))
    s.add(Distinct(s1, s2))
    s.add(Distinct(hc1, hc2))
    s.add(Distinct(ht1, ht2))
    s.add(Distinct(sm1, sm2))
    s.add(Distinct(f1, f2))

    # Clue 1: Soccer is not in the second house -> must be in house 1
    s.add(s1 == soccer)

    # Clue 2: Desert smoothie lover is directly left of very short person
    s.add(sm1 == desert)
    s.add(ht2 == very_short)

    # Clue 3: Very short person has brown hair
    s.add(hc2 == brown)

    # Clue 4: Carnations lover is desert smoothie lover
    s.add(f1 == carnations)

    # Clue 5: Eric and brown hair person are next to each other
    s.add(Or(
        And(n1 == Eric, hc2 == brown),
        And(n2 == Eric, hc1 == brown)
    ))

    if s.check() == sat:
        model = s.model()
        # Function to get the string value from a Z3 model
        def get_value(var):
            val = model[var]
            return val.decl().name()

        row1 = [
            "1",
            get_value(n1),
            get_value(s1),
            get_value(hc1),
            get_value(ht1),
            get_value(sm1),
            get_value(f1)
        ]
        row2 = [
            "2",
            get_value(n2),
            get_value(s2),
            get_value(hc2),
            get_value(ht2),
            get_value(sm2),
            get_value(f2)
        ]

        solution = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
                "rows": [row1, row2]
            }
        }

        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()