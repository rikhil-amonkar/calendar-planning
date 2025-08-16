import json
from z3 import *

# Define EnumSorts for each attribute
Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
Sport, (Basketball, Soccer) = EnumSort('Sport', ['basketball', 'soccer'])
HairColor, (Brown, Black) = EnumSort('HairColor', ['brown', 'black'])
Height, (VeryShort, Short) = EnumSort('Height', ['very short', 'short'])
Smoothie, (Desert, Cherry) = EnumSort('Smoothie', ['desert', 'cherry'])
Flower, (Daffodils, Carnations) = EnumSort('Flower', ['daffodils', 'carnations'])

# Create variables for house 1 and 2
name1, name2 = Consts('name1 name2', Name)
sport1, sport2 = Consts('sport1 sport2', Sport)
hair_color1, hair_color2 = Consts('hair_color1 hair_color2', HairColor)
height1, height2 = Consts('height1 height2', Height)
smoothie1, smoothie2 = Consts('smoothie1 smoothie2', Smoothie)
flower1, flower2 = Consts('flower1 flower2', Flower)

solver = Solver()

# Uniqueness constraints for each attribute
solver.add(name1 != name2)
solver.add(sport1 != sport2)
solver.add(hair_color1 != hair_color2)
solver.add(height1 != height2)
solver.add(smoothie1 != smoothie2)
solver.add(flower1 != flower2)

# Add clues as constraints
# Clue 1: Soccer is not in the second house
solver.add(sport2 != Soccer)

# Clue 2: Desert smoothie lover is directly left of the very short person
solver.add(smoothie1 == Desert)
solver.add(height2 == VeryShort)

# Clue 3: Very short person has brown hair
solver.add(hair_color2 == Brown)

# Clue 4: Carnations lover is the Desert smoothie lover
solver.add(flower1 == Carnations)

# Clue 5: Eric and the brown-haired person are next to each other
solver.add(name1 == Eric)

# Check for solution
if solver.check() == sat:
    m = solver.model()
    
    # Extract values for house 1
    h1_name = str(m.evaluate(name1))
    h1_sport = str(m.evaluate(sport1))
    h1_hair = str(m.evaluate(hair_color1))
    h1_height = str(m.evaluate(height1))
    h1_smoothie = str(m.evaluate(smoothie1))
    h1_flower = str(m.evaluate(flower1))
    
    # Extract values for house 2
    h2_name = str(m.evaluate(name2))
    h2_sport = str(m.evaluate(sport2))
    h2_hair = str(m.evaluate(hair_color2))
    h2_height = str(m.evaluate(height2))
    h2_smoothie = str(m.evaluate(smoothie2))
    h2_flower = str(m.evaluate(flower2))
    
    # Construct the JSON solution
    solution = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
            "rows": [
                ["1", h1_name, h1_sport, h1_hair, h1_height, h1_smoothie, h1_flower],
                ["2", h2_name, h2_sport, h2_hair, h2_height, h2_smoothie, h2_flower]
            ]
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")