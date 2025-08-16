from z3 import *
import json

def main():
    s = Solver()

    # Define enums for each attribute
    Name, (arnold, eric, peter) = EnumSort('Name', ['Arnold', 'Eric', 'Peter'])
    Flower, (carnations, lilies, daffodils) = EnumSort('Flower', ['carnations', 'lilies', 'daffodils'])
    HairColor, (black, brown, blonde) = EnumSort('HairColor', ['black', 'brown', 'blonde'])
    Sport, (soccer, basketball, tennis) = EnumSort('Sport', ['soccer', 'basketball', 'tennis'])
    HouseStyle, (colonial, ranch, victorian) = EnumSort('HouseStyle', ['colonial', 'ranch', 'victorian'])
    Pet, (fish, dog, cat) = EnumSort('Pet', ['fish', 'dog', 'cat'])

    # Create attributes for each house (0-indexed for houses 1,2,3)
    attrs = {
        'Name': [Const(f'Name_{i}', Name) for i in range(3)],
        'Flower': [Const(f'Flower_{i}', Flower) for i in range(3)],
        'HairColor': [Const(f'HairColor_{i}', HairColor) for i in range(3)],
        'FavoriteSport': [Const(f'Sport_{i}', Sport) for i in range(3)],
        'HouseStyle': [Const(f'HouseStyle_{i}', HouseStyle) for i in range(3)],
        'Pet': [Const(f'Pet_{i}', Pet) for i in range(3)]
    }

    # Ensure all attributes are unique per category
    for key in attrs:
        s.add(Distinct(attrs[key]))

    # Clue 1: Cat owner loves soccer
    for i in range(3):
        s.add((attrs['Pet'][i] == cat) == (attrs['FavoriteSport'][i] == soccer))

    # Clue 2: Blonde hair in house 2 (index 1)
    s.add(attrs['HairColor'][1] == blonde)

    # Clue 3: Daffodils lover has blonde hair
    for i in range(3):
        s.add((attrs['Flower'][i] == daffodils) == (attrs['HairColor'][i] == blonde))

    # Clue 4: Peter loves basketball
    for i in range(3):
        s.add((attrs['Name'][i] == peter) == (attrs['FavoriteSport'][i] == basketball))

    # Clue 5: Arnold is directly left of ranch-style home
    s.add(Or(
        And(attrs['Name'][0] == arnold, attrs['HouseStyle'][1] == ranch),
        And(attrs['Name'][1] == arnold, attrs['HouseStyle'][2] == ranch)
    ))

    # Clue 6: Dog owner loves basketball
    for i in range(3):
        s.add((attrs['Pet'][i] == dog) == (attrs['FavoriteSport'][i] == basketball))

    # Clue 7: Carnations lover is directly left of blonde hair (house 2)
    s.add(attrs['Flower'][0] == carnations)

    # Clue 8: Soccer lover in house 3 (index 2)
    s.add(attrs['FavoriteSport'][2] == soccer)

    # Clue 9: Arnold is left of black-haired person
    s.add(Or(
        And(attrs['Name'][0] == arnold, Or(attrs['HairColor'][1] == black, attrs['HairColor'][2] == black)),
        And(attrs['Name'][1] == arnold, attrs['HairColor'][2] == black)
    ))

    # Clue 10: Colonial-style house in house 3 (index 2)
    s.add(attrs['HouseStyle'][2] == colonial)

    # Solve and output
    if s.check() == sat:
        m = s.model()
        # Mapping from Z3 constants to strings
        name_map = { arnold: 'Arnold', eric: 'Eric', peter: 'Peter' }
        flower_map = { carnations: 'carnations', lilies: 'lilies', daffodils: 'daffodils' }
        hair_map = { black: 'black', brown: 'brown', blonde: 'blonde' }
        sport_map = { soccer: 'soccer', basketball: 'basketball', tennis: 'tennis' }
        style_map = { colonial: 'colonial', ranch: 'ranch', victorian: 'victorian' }
        pet_map = { fish: 'fish', dog: 'dog', cat: 'cat' }

        rows = []
        for i in range(3):
            name_val = m[attrs['Name'][i]]
            flower_val = m[attrs['Flower'][i]]
            hair_val = m[attrs['HairColor'][i]]
            sport_val = m[attrs['FavoriteSport'][i]]
            style_val = m[attrs['HouseStyle'][i]]
            pet_val = m[attrs['Pet'][i]]

            row = [
                str(i+1),
                name_map[name_val],
                flower_map[flower_val],
                hair_map[hair_val],
                sport_map[sport_val],
                style_map[style_val],
                pet_map[pet_val]
            ]
            rows.append(row)

        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()