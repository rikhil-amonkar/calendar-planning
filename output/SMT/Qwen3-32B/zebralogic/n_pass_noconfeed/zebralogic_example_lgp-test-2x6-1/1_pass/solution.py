import json
from z3 import *

def main():
    # Define EnumSorts
    Names, (Arnold, Eric) = EnumSort('Names', ['Arnold', 'Eric'])
    Sports, (basketball, soccer) = EnumSort('Sports', ['basketball', 'soccer'])
    HairColors, (brown, black) = EnumSort('HairColors', ['brown', 'black'])
    Heights, (very_short, short_height) = EnumSort('Heights', ['very short', 'short'])
    Smoothies, (desert, cherry) = EnumSort('Smoothies', ['desert', 'cherry'])
    Flowers, (daffodils, carnations) = EnumSort('Flowers', ['daffodils', 'carnations'])

    # Variables for house 1 and 2
    name1 = Const('name1', Names)
    sport1 = Const('sport1', Sports)
    hair_color1 = Const('hair_color1', HairColors)
    height1 = Const('height1', Heights)
    smoothie1 = Const('smoothie1', Smoothies)
    flower1 = Const('flower1', Flowers)
    name2 = Const('name2', Names)
    sport2 = Const('sport2', Sports)
    hair_color2 = Const('hair_color2', HairColors)
    height2 = Const('height2', Heights)
    smoothie2 = Const('smoothie2', Smoothies)
    flower2 = Const('flower2', Flowers)

    s = Solver()

    # Add distinct constraints for each category
    s.add(Distinct(name1, name2))
    s.add(Distinct(sport1, sport2))
    s.add(Distinct(hair_color1, hair_color2))
    s.add(Distinct(height1, height2))
    s.add(Distinct(smoothie1, smoothie2))
    s.add(Distinct(flower1, flower2))

    # Add puzzle constraints
    s.add(sport2 != soccer)  # Clue 1
    s.add(smoothie1 == desert)  # Clue 2
    s.add(height2 == very_short)  # Clue 2
    s.add(hair_color2 == brown)  # Clue 3
    s.add(flower1 == carnations)  # Clue 4
    s.add(name1 == Eric)  # Clue 5

    # Check if satisfiable
    if s.check() == sat:
        model = s.model()

        # Prepare the rows
        rows = []
        for house_num, name, sport, hair_color, height, smoothie, flower in [
            (1, name1, sport1, hair_color1, height1, smoothie1, flower1),
            (2, name2, sport2, hair_color2, height2, smoothie2, flower2)
        ]:
            row = [
                str(house_num),
                str(model.eval(name)),
                str(model.eval(sport)),
                str(model.eval(hair_color)),
                str(model.eval(height)),
                str(model.eval(smoothie)),
                str(model.eval(flower))
            ]
            rows.append(row)

        # Build JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
                "rows": rows
            }
        }

        # Output JSON
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()