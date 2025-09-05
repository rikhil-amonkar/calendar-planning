import z3
import json

def main():
    # Create a solver instance
    solver = z3.Solver()

    # Define the attributes using EnumSort and unpack constants
    Name, (Arnold, Eric, Peter) = z3.EnumSort('Name', ['Arnold', 'Eric', 'Peter'])
    Flower, (Carnations, Lilies, Daffodils) = z3.EnumSort('Flower', ['carnations', 'lilies', 'daffodils'])
    HairColor, (Black, Brown, Blonde) = z3.EnumSort('HairColor', ['black', 'brown', 'blonde'])
    FavoriteSport, (Soccer, Basketball, Tennis) = z3.EnumSort('FavoriteSport', ['soccer', 'basketball', 'tennis'])
    HouseStyle, (Colonial, Ranch, Victorian) = z3.EnumSort('HouseStyle', ['colonial', 'ranch', 'victorian'])
    Pet, (Fish, Dog, Cat) = z3.EnumSort('Pet', ['fish', 'dog', 'cat'])

    # Create variables for each house and each attribute
    houses = [1, 2, 3]
    names = [z3.Const(f'name_{i}', Name) for i in houses]
    flowers = [z3.Const(f'flower_{i}', Flower) for i in houses]
    hair_colors = [z3.Const(f'hair_color_{i}', HairColor) for i in houses]
    favorite_sports = [z3.Const(f'favorite_sport_{i}', FavoriteSport) for i in houses]
    house_styles = [z3.Const(f'house_style_{i}', HouseStyle) for i in houses]
    pets = [z3.Const(f'pet_{i}', Pet) for i in houses]

    # Add constraints that all attributes are distinct within their category
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(flowers))
    solver.add(z3.Distinct(hair_colors))
    solver.add(z3.Distinct(favorite_sports))
    solver.add(z3.Distinct(house_styles))
    solver.add(z3.Distinct(pets))

    # Clue 1: The person who has a cat is the person who loves soccer.
    for i in range(3):
        solver.add(z3.Implies(pets[i] == Cat, favorite_sports[i] == Soccer))

    # Clue 2: The person who has blonde hair is in the second house.
    solver.add(hair_colors[1] == Blonde)

    # Clue 3: The person who loves a bouquet of daffodils is the person who has blonde hair.
    for i in range(3):
        solver.add(z3.Implies(flowers[i] == Daffodils, hair_colors[i] == Blonde))

    # Clue 4: Peter is the person who loves basketball.
    for i in range(3):
        solver.add(z3.Implies(names[i] == Peter, favorite_sports[i] == Basketball))

    # Clue 5: Arnold is directly left of the person in a ranch-style home.
    solver.add(z3.Or([z3.And(names[i] == Arnold, house_styles[i+1] == Ranch) for i in [0,1]]))

    # Clue 6: The person who owns a dog is the person who loves basketball.
    for i in range(3):
        solver.add(z3.Implies(pets[i] == Dog, favorite_sports[i] == Basketball))

    # Clue 7: The person who loves a carnations arrangement is directly left of the person who has blonde hair.
    solver.add(flowers[0] == Carnations)

    # Clue 8: The person who loves soccer is in the third house.
    solver.add(favorite_sports[2] == Soccer)

    # Clue 9: Arnold is somewhere to the left of the person who has black hair.
    arnold_index = z3.Int('arnold_index')
    black_hair_index = z3.Int('black_hair_index')
    solver.add(arnold_index >= 1, arnold_index <= 3)
    solver.add(black_hair_index >= 1, black_hair_index <= 3)
    solver.add(arnold_index < black_hair_index)
    for i in range(3):
        solver.add(z3.Implies(names[i] == Arnold, arnold_index == i+1))
        solver.add(z3.Implies(hair_colors[i] == Black, black_hair_index == i+1))

    # Clue 10: The person living in a colonial-style house is in the third house.
    solver.add(house_styles[2] == Colonial)

    # Check for a solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare the rows
        rows = []
        for i in range(3):
            house_num = str(i+1)
            # Get the string representation using decl().name()
            name_val = model[names[i]].decl().name()
            flower_val = model[flowers[i]].decl().name()
            hair_color_val = model[hair_colors[i]].decl().name()
            favorite_sport_val = model[favorite_sports[i]].decl().name()
            house_style_val = model[house_styles[i]].decl().name()
            pet_val = model[pets[i]].decl().name()
            rows.append([house_num, name_val, flower_val, hair_color_val, favorite_sport_val, house_style_val, pet_val])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()