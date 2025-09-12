import json
from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define enums for each attribute
    Name = EnumSort('Name', ['Arnold', 'Eric'])
    FavoriteSport = EnumSort('FavoriteSport', ['basketball', 'soccer'])
    HairColor = EnumSort('HairColor', ['brown', 'black'])
    Height = EnumSort('Height', ['very short', 'short'])
    Smoothie = EnumSort('Smoothie', ['desert', 'cherry'])
    Flower = EnumSort('Flower', ['daffodils', 'carnations'])
    
    # Create constants for enum values
    Arnold, Eric = Consts('Arnold Eric', Name)
    basketball, soccer = Consts('basketball soccer', FavoriteSport)
    brown, black = Consts('brown black', HairColor)
    very_short, short = Consts('very short short', Height)
    desert, cherry = Consts('desert cherry', Smoothie)
    daffodils, carnations = Consts('daffodils carnations', Flower)
    
    # Create variables for each house's attributes
    name = [Const(f'name_{i}', Name) for i in range(1, 3)]
    sport = [Const(f'sport_{i}', FavoriteSport) for i in range(1, 3)]
    hair = [Const(f'hair_{i}', HairColor) for i in range(1, 3)]
    height = [Const(f'height_{i}', Height) for i in range(1, 3)]
    smoothie = [Const(f'smoothie_{i}', Smoothie) for i in range(1, 3)]
    flower = [Const(f'flower_{i}', Flower) for i in range(1, 3)]
    
    # Add uniqueness constraints for each attribute
    s.add(Distinct(name))
    s.add(Distinct(sport))
    s.add(Distinct(hair))
    s.add(Distinct(height))
    s.add(Distinct(smoothie))
    s.add(Distinct(flower))
    
    # Clue 1: The person who loves soccer is not in the second house.
    s.add(sport[1] != soccer)
    
    # Clue 2: The Desert smoothie lover is directly left of the person who is very short.
    s.add(smoothie[0] == desert)
    s.add(height[1] == very_short)
    
    # Clue 3: The person who is very short is the person who has brown hair.
    s.add(If(height[0] == very_short, hair[0] == brown, hair[1] == brown))
    
    # Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
    s.add(If(smoothie[0] == desert, flower[0] == carnations, flower[1] == carnations))
    
    # Clue 5: Eric and the person who has brown hair are next to each other.
    s.add(Or(
        And(name[0] == Eric, hair[1] == brown),
        And(name[1] == Eric, hair[0] == brown)
    ))
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        
        # Function to get string value from model
        def get_value(var, model):
            return str(model[var]).split('!')[0]
        
        # Prepare rows
        rows = []
        for i in range(2):
            row = [
                str(i+1),
                get_value(name[i], m),
                get_value(sport[i], m),
                get_value(hair[i], m),
                get_value(height[i], m),
                get_value(smoothie[i], m),
                get_value(flower[i], m)
            ]
            rows.append(row)
        
        # Create solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
                "rows": rows
            }
        }
        
        # Output JSON
        print(json.dumps(solution, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()