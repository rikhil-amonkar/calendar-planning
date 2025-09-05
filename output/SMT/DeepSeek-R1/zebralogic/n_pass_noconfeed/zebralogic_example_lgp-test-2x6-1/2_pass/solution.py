from z3 import *
import json

def main():
    # Define the attributes and their possible values using EnumSort, unpacking the sort and constants
    NameSort, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    FavoriteSportSort, (basketball, soccer) = EnumSort('FavoriteSport', ['basketball', 'soccer'])
    HairColorSort, (brown, black) = EnumSort('HairColor', ['brown', 'black'])
    HeightSort, (very_short, short) = EnumSort('Height', ['very_short', 'short'])
    SmoothieSort, (desert, cherry) = EnumSort('Smoothie', ['desert', 'cherry'])
    FlowerSort, (daffodils, carnations) = EnumSort('Flower', ['daffodils', 'carnations'])
    
    # Create variables for each attribute per house using the correct sorts
    names = [Const(f'name_{i}', NameSort) for i in range(2)]
    sports = [Const(f'sport_{i}', FavoriteSportSort) for i in range(2)]
    hairs = [Const(f'hair_{i}', HairColorSort) for i in range(2)]
    heights = [Const(f'height_{i}', HeightSort) for i in range(2)]
    smoothies = [Const(f'smoothie_{i}', SmoothieSort) for i in range(2)]
    flowers = [Const(f'flower_{i}', FlowerSort) for i in range(2)]
    
    s = Solver()
    
    # Each attribute must have unique values across houses
    s.add(Distinct(names))
    s.add(Distinct(sports))
    s.add(Distinct(hairs))
    s.add(Distinct(heights))
    s.add(Distinct(smoothies))
    s.add(Distinct(flowers))
    
    # Clue 1: The person who loves soccer is not in the second house.
    s.add(sports[0] == soccer)
    
    # Clue 2: The Desert smoothie lover is directly left of the person who is very short.
    s.add(smoothies[0] == desert)
    s.add(heights[1] == very_short)
    
    # Clue 3: The person who is very short is the person who has brown hair.
    s.add(hairs[1] == brown)
    
    # Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
    s.add(flowers[0] == carnations)
    
    # Clue 5: Eric and the person who has brown hair are next to each other.
    # Since brown hair is in house2 (from clue 3), Eric must be in house1
    s.add(names[0] == Eric)
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(2):
            # Convert Z3 values to strings
            name_val = m.eval(names[i])
            if name_val.eq(Arnold):
                name_str = "Arnold"
            else:
                name_str = "Eric"
                
            sport_val = m.eval(sports[i])
            if sport_val.eq(basketball):
                sport_str = "basketball"
            else:
                sport_str = "soccer"
                
            hair_val = m.eval(hairs[i])
            if hair_val.eq(brown):
                hair_str = "brown"
            else:
                hair_str = "black"
                
            height_val = m.eval(heights[i])
            if height_val.eq(very_short):
                height_str = "very short"
            else:
                height_str = "short"
                
            smoothie_val = m.eval(smoothies[i])
            if smoothie_val.eq(desert):
                smoothie_str = "desert"
            else:
                smoothie_str = "cherry"
                
            flower_val = m.eval(flowers[i])
            if flower_val.eq(daffodils):
                flower_str = "daffodils"
            else:
                flower_str = "carnations"
                
            rows.append([str(i+1), name_str, sport_str, hair_str, height_str, smoothie_str, flower_str])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()