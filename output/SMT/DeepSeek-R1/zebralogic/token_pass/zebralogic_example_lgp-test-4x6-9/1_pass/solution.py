import json
from z3 import *

def main():
    # Create solver
    s = Solver()

    # Define EnumSorts for each category
    NameSort, (Peter, Arnold, Eric, Alice) = EnumSort('Name', ['Peter', 'Arnold', 'Eric', 'Alice'])
    FlowerSort, (daffodils, carnations, roses, lilies) = EnumSort('Flower', ['daffodils', 'carnations', 'roses', 'lilies'])
    HeightSort, (very_short, short, tall, average) = EnumSort('Height', ['very_short', 'short', 'tall', 'average'])
    MotherSort, (Janelle, Kailyn, Holly, Aniya) = EnumSort('Mother', ['Janelle', 'Kailyn', 'Holly', 'Aniya'])
    OccupationSort, (engineer, doctor, teacher, artist) = EnumSort('Occupation', ['engineer', 'doctor', 'teacher', 'artist'])
    SportSort, (swimming, basketball, tennis, soccer) = EnumSort('Sport', ['swimming', 'basketball', 'tennis', 'soccer'])

    # Create attributes for each house (4 houses)
    names = [Const(f'name_{i}', NameSort) for i in range(1,5)]
    flowers = [Const(f'flower_{i}', FlowerSort) for i in range(1,5)]
    heights = [Const(f'height_{i}', HeightSort) for i in range(1,5)]
    mothers = [Const(f'mother_{i}', MotherSort) for i in range(1,5)]
    occupations = [Const(f'occupation_{i}', OccupationSort) for i in range(1,5)]
    sports = [Const(f'sport_{i}', SportSort) for i in range(1,5)]

    # Add distinct constraints
    s.add(Distinct(names))
    s.add(Distinct(flowers))
    s.add(Distinct(heights))
    s.add(Distinct(mothers))
    s.add(Distinct(occupations))
    s.add(Distinct(sports))

    # Clue 1: Swimming lover is rose lover
    for i in range(4):
        s.add(sports[i] == swimming == (flowers[i] == roses))

    # Clue 2: Rose lover is Eric
    for i in range(4):
        s.add(flowers[i] == roses == (names[i] == Eric))

    # Clue 3: Arnold is tall
    for i in range(4):
        s.add(names[i] == Arnold == (heights[i] == tall))

    # Clue 4: Daffodils right of engineer
    s.add(Or([And(flowers[i] == daffodils, occupations[j] == engineer, i > j) for i in range(4) for j in range(4)]))

    # Clue 5: Soccer lover is short
    for i in range(4):
        s.add(sports[i] == soccer == (heights[i] == short))

    # Clue 6: Teacher in first house
    s.add(occupations[0] == teacher)

    # Clue 7: Janelle's mother is carnations lover
    for i in range(4):
        s.add(mothers[i] == Janelle == (flowers[i] == carnations))

    # Clue 8: Basketball lover is average height
    for i in range(4):
        s.add(sports[i] == basketball == (heights[i] == average))

    # Clue 9: Arnold not in third house
    s.add(names[2] != Arnold)

    # Clue 10: Holly's mother right of average height
    s.add(Or([And(heights[i] == average, mothers[j] == Holly, j > i) for i in range(4) for j in range(4)]))

    # Clue 11: Peter is doctor
    for i in range(4):
        s.add(names[i] == Peter == (occupations[i] == doctor))

    # Clue 12: Aniya's mother is Alice
    for i in range(4):
        s.add(mothers[i] == Aniya == (names[i] == Alice))

    # Clue 13: Arnold is lilies lover
    for i in range(4):
        s.add(names[i] == Arnold == (flowers[i] == lilies))

    # Check and get model
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(4):
            house = str(i+1)
            name = m.eval(names[i]).decl().name()
            flower = m.eval(flowers[i]).decl().name()
            height = m.eval(heights[i]).decl().name()
            mother = m.eval(mothers[i]).decl().name()
            occupation = m.eval(occupations[i]).decl().name()
            sport = m.eval(sports[i]).decl().name()
            rows.append([house, name, flower, height, mother, occupation, sport])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()