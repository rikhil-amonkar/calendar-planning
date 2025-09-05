import json
from z3 import *

def main():
    # Create the solver
    solver = Solver()

    # Define the attributes and their possible values
    names = ['Peter', 'Eric', 'Alice', 'Arnold']
    educations = ['bachelor', 'high school', 'associate', 'master']
    music_genres = ['jazz', 'rock', 'pop', 'classical']
    colors = ['green', 'red', 'yellow', 'white']
    flowers = ['lilies', 'carnations', 'daffodils', 'roses']

    # Create Z3 enums for each category and get both the sort and constants
    NameSort, name_consts = EnumSort('Name', names)
    EducationSort, education_consts = EnumSort('Education', educations)
    MusicGenreSort, music_consts = EnumSort('MusicGenre', music_genres)
    ColorSort, color_consts = EnumSort('Color', colors)
    FlowerSort, flower_consts = EnumSort('Flower', flowers)

    # Create variables for each house and each attribute using the correct sorts
    house_vars = []
    for i in range(1, 5):
        name_var = Const(f'name_{i}', NameSort)
        education_var = Const(f'education_{i}', EducationSort)
        music_var = Const(f'music_{i}', MusicGenreSort)
        color_var = Const(f'color_{i}', ColorSort)
        flower_var = Const(f'flower_{i}', FlowerSort)
        house_vars.append((name_var, education_var, music_var, color_var, flower_var))

    # All attributes must be distinct within their categories
    solver.add(Distinct([var for var, _, _, _, _ in house_vars]))
    solver.add(Distinct([var for _, var, _, _, _ in house_vars]))
    solver.add(Distinct([var for _, _, var, _, _ in house_vars]))
    solver.add(Distinct([var for _, _, _, var, _ in house_vars]))
    solver.add(Distinct([var for _, _, _, _, var in house_vars]))

    # Unpack the house variables for easier reference
    name1, education1, music1, color1, flower1 = house_vars[0]
    name2, education2, music2, color2, flower2 = house_vars[1]
    name3, education3, music3, color3, flower3 = house_vars[2]
    name4, education4, music4, color4, flower4 = house_vars[3]

    # Clue 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils.
    bachelor = education_consts[educations.index('bachelor')]
    daffodils = flower_consts[flowers.index('daffodils')]
    solver.add(Or(
        And(education1 == bachelor, flower1 == daffodils),
        And(education2 == bachelor, flower2 == daffodils),
        And(education3 == bachelor, flower3 == daffodils),
        And(education4 == bachelor, flower4 == daffodils)
    ))

    # Clue 2: The person who loves a carnations arrangement is not in the first house.
    carnations = flower_consts[flowers.index('carnations')]
    solver.add(flower1 != carnations)

    # Clue 3: The person with a master's degree is Alice.
    master = education_consts[educations.index('master')]
    alice = name_consts[names.index('Alice')]
    solver.add(Or(
        And(education1 == master, name1 == alice),
        And(education2 == master, name2 == alice),
        And(education3 == master, name3 == alice),
        And(education4 == master, name4 == alice)
    ))

    # Clue 4: The person with a master's degree is directly left of the person who loves classical music.
    classical = music_consts[music_genres.index('classical')]
    solver.add(Or(
        And(education1 == master, music2 == classical),
        And(education2 == master, music3 == classical),
        And(education3 == master, music4 == classical)
    ))

    # Clue 5: Eric is not in the second house.
    eric = name_consts[names.index('Eric')]
    solver.add(name2 != eric)

    # Clue 6: Arnold is not in the third house.
    arnold = name_consts[names.index('Arnold')]
    solver.add(name3 != arnold)

    # Clue 7: The person who loves yellow is directly left of the person who loves the rose bouquet.
    yellow = color_consts[colors.index('yellow')]
    roses = flower_consts[flowers.index('roses')]
    solver.add(Or(
        And(color1 == yellow, flower2 == roses),
        And(color2 == yellow, flower3 == roses),
        And(color3 == yellow, flower4 == roses)
    ))

    # Clue 8: The person who loves pop music is in the second house.
    pop = music_consts[music_genres.index('pop')]
    solver.add(music2 == pop)

    # Clue 9: The person with an associate's degree is not in the fourth house.
    associate = education_consts[educations.index('associate')]
    solver.add(education4 != associate)

    # Clue 10: The person who loves a carnations arrangement is not in the fourth house.
    solver.add(flower4 != carnations)

    # Clue 11: The person whose favorite color is red is directly left of the person who loves white.
    red = color_consts[colors.index('red')]
    white = color_consts[colors.index('white')]
    solver.add(Or(
        And(color1 == red, color2 == white),
        And(color2 == red, color3 == white),
        And(color3 == red, color4 == white)
    ))

    # Clue 12: The person whose favorite color is red is the person who loves rock music.
    rock = music_consts[music_genres.index('rock')]
    solver.add(Or(
        And(color1 == red, music1 == rock),
        And(color2 == red, music2 == rock),
        And(color3 == red, music3 == rock),
        And(color4 == red, music4 == rock)
    ))

    # Clue 13: Arnold is the person who loves yellow.
    solver.add(Or(
        And(name1 == arnold, color1 == yellow),
        And(name2 == arnold, color2 == yellow),
        And(name3 == arnold, color3 == yellow),
        And(name4 == arnold, color4 == yellow)
    ))

    # Clue 14: The person who loves a bouquet of daffodils is the person who loves yellow.
    solver.add(Or(
        And(flower1 == daffodils, color1 == yellow),
        And(flower2 == daffodils, color2 == yellow),
        And(flower3 == daffodils, color3 == yellow),
        And(flower4 == daffodils, color4 == yellow)
    ))

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map the Z3 constants back to strings
        def get_value(var, constants, string_list):
            for i, c in enumerate(constants):
                if model.eval(var).eq(model.eval(c)):
                    return string_list[i]
            return None

        # Prepare the solution rows
        rows = []
        for i, (name_var, education_var, music_var, color_var, flower_var) in enumerate(house_vars, start=1):
            name_val = get_value(name_var, name_consts, names)
            education_val = get_value(education_var, education_consts, educations)
            music_val = get_value(music_var, music_consts, music_genres)
            color_val = get_value(color_var, color_consts, colors)
            flower_val = get_value(flower_var, flower_consts, flowers)
            rows.append([str(i), name_val, education_val, music_val, color_val, flower_val])
        
        # Format the solution as JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()