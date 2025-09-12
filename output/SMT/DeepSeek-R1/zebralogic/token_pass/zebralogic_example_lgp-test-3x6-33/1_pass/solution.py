import json
from z3 import *

def main():
    # Create the sorts for each attribute
    NameSort, (arnold, eric, peter) = EnumSort('Name', ['Arnold', 'Eric', 'Peter'])
    FlowerSort, (carnations, lilies, daffodils) = EnumSort('Flower', ['carnations', 'lilies', 'daffodils'])
    HairSort, (black, brown, blonde) = EnumSort('Hair', ['black', 'brown', 'blonde'])
    SportSort, (soccer, basketball, tennis) = EnumSort('Sport', ['soccer', 'basketball', 'tennis'])
    HouseStyleSort, (colonial, ranch, victorian) = EnumSort('HouseStyle', ['colonial', 'ranch', 'victorian'])
    PetSort, (fish, dog, cat) = EnumSort('Pet', ['fish', 'dog', 'cat'])

    # Create variables for each house (index 0 for house1, 1 for house2, 2 for house3)
    n = [Const(f'n{i}', NameSort) for i in range(3)]
    f = [Const(f'f{i}', FlowerSort) for i in range(3)]
    hc = [Const(f'hc{i}', HairSort) for i in range(3)]
    s = [Const(f's{i}', SportSort) for i in range(3)]
    hs = [Const(f'hs{i}', HouseStyleSort) for i in range(3)]
    p = [Const(f'p{i}', PetSort) for i in range(3)]

    solver = Solver()

    # Each attribute must be unique per category
    solver.add(Distinct(n))
    solver.add(Distinct(f))
    solver.add(Distinct(hc))
    solver.add(Distinct(s))
    solver.add(Distinct(hs))
    solver.add(Distinct(p))

    # Clue 1: The person who has a cat is the person who loves soccer.
    for i in range(3):
        solver.add(Implies(p[i] == cat, s[i] == soccer))

    # Clue 2: The person who has blonde hair is in the second house.
    solver.add(hc[1] == blonde)

    # Clue 3: The person who loves a bouquet of daffodils is the person who has blonde hair.
    for i in range(3):
        solver.add(Implies(f[i] == daffodils, hc[i] == blonde))

    # Clue 4: Peter is the person who loves basketball.
    for i in range(3):
        solver.add(Implies(n[i] == peter, s[i] == basketball))

    # Clue 5: Arnold is directly left of the person in a ranch-style home.
    solver.add(Or(
        And(n[0] == arnold, hs[1] == ranch),
        And(n[1] == arnold, hs[2] == ranch)
    ))

    # Clue 6: The person who owns a dog is the person who loves basketball.
    for i in range(3):
        solver.add(Implies(p[i] == dog, s[i] == basketball))

    # Clue 7: The person who loves a carnations arrangement is directly left of the person who has blonde hair.
    solver.add(f[0] == carnations)

    # Clue 8: The person who loves soccer is in the third house.
    solver.add(s[2] == soccer)

    # Clue 9: Arnold is somewhere to the left of the person who has black hair.
    # Arnold can be in house1 or house2, and black hair must be right of Arnold
    solver.add(Or(
        And(n[0] == arnold, Or(hc[1] == black, hc[2] == black)),
        And(n[1] == arnold, hc[2] == black)
    ))

    # Clue 10: The person living in a colonial-style house is in the third house.
    solver.add(hs[2] == colonial)

    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        
        # Map back to string values
        name_map = {arnold: 'Arnold', eric: 'Eric', peter: 'Peter'}
        flower_map = {carnations: 'carnations', lilies: 'lilies', daffodils: 'daffodils'}
        hair_map = {black: 'black', brown: 'brown', blonde: 'blonde'}
        sport_map = {soccer: 'soccer', basketball: 'basketball', tennis: 'tennis'}
        style_map = {colonial: 'colonial', ranch: 'ranch', victorian: 'victorian'}
        pet_map = {fish: 'fish', dog: 'dog', cat: 'cat'}
        
        rows = []
        for i in range(3):
            house_num = str(i+1)
            name_val = name_map[model.evaluate(n[i])]
            flower_val = flower_map[model.evaluate(f[i])]
            hair_val = hair_map[model.evaluate(hc[i])]
            sport_val = sport_map[model.evaluate(s[i])]
            style_val = style_map[model.evaluate(hs[i])]
            pet_val = pet_map[model.evaluate(p[i])]
            rows.append([house_num, name_val, flower_val, hair_val, sport_val, style_val, pet_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()