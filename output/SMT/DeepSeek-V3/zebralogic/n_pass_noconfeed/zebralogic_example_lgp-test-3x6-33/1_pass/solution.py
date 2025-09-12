from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Define the number of houses
    n_houses = 3
    
    # Define the attributes
    names = ['Arnold', 'Eric', 'Peter']
    flowers = ['carnations', 'lilies', 'daffodils']
    hair_colors = ['black', 'brown', 'blonde']
    sports = ['soccer', 'basketball', 'tennis']
    house_styles = ['colonial', 'ranch', 'victorian']
    pets = ['fish', 'dog', 'cat']
    
    # Create integer variables for each attribute (position in house 1, 2, 3)
    name_vars = [Int(f'name_{name}') for name in names]
    flower_vars = [Int(f'flower_{flower}') for flower in flowers]
    hair_vars = [Int(f'hair_{color}') for color in hair_colors]
    sport_vars = [Int(f'sport_{sport}') for sport in sports]
    house_style_vars = [Int(f'house_style_{style}') for style in house_styles]
    pet_vars = [Int(f'pet_{pet}') for pet in pets]
    
    # Each attribute must be in exactly one house (1, 2, or 3)
    for var_list in [name_vars, flower_vars, hair_vars, sport_vars, house_style_vars, pet_vars]:
        s.add(Distinct(var_list))
        for var in var_list:
            s.add(And(var >= 1, var <= n_houses))
    
    # Clue 1: The person who has a cat is the person who loves soccer.
    s.add(pet_vars[pets.index('cat')] == sport_vars[sports.index('soccer')])
    
    # Clue 2: The person who has blonde hair is in the second house.
    s.add(hair_vars[hair_colors.index('blonde')] == 2)
    
    # Clue 3: The person who loves a bouquet of daffodils is the person who has blonde hair.
    s.add(flower_vars[flowers.index('daffodils')] == hair_vars[hair_colors.index('blonde')])
    
    # Clue 4: Peter is the person who loves basketball.
    s.add(name_vars[names.index('Peter')] == sport_vars[sports.index('basketball')])
    
    # Clue 5: Arnold is directly left of the person in a ranch-style home.
    s.add(name_vars[names.index('Arnold')] + 1 == house_style_vars[house_styles.index('ranch')])
    
    # Clue 6: The person who owns a dog is the person who loves basketball.
    s.add(pet_vars[pets.index('dog')] == sport_vars[sports.index('basketball')])
    
    # Clue 7: The person who loves a carnations arrangement is directly left of the person who has blonde hair.
    s.add(flower_vars[flowers.index('carnations')] + 1 == hair_vars[hair_colors.index('blonde')])
    
    # Clue 8: The person who loves soccer is in the third house.
    s.add(sport_vars[sports.index('soccer')] == 3)
    
    # Clue 9: Arnold is somewhere to the left of the person who has black hair.
    s.add(name_vars[names.index('Arnold')] < hair_vars[hair_colors.index('black')])
    
    # Clue 10: The person living in a colonial-style house is in the third house.
    s.add(house_style_vars[house_styles.index('colonial')] == 3)
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        
        # Create a mapping from house number to attributes
        houses = {1: {}, 2: {}, 3: {}}
        
        # Extract values for each attribute
        for i, name in enumerate(names):
            house_num = model.eval(name_vars[i]).as_long()
            houses[house_num]['Name'] = name
        
        for i, flower in enumerate(flowers):
            house_num = model.eval(flower_vars[i]).as_long()
            houses[house_num]['Flower'] = flower
        
        for i, color in enumerate(hair_colors):
            house_num = model.eval(hair_vars[i]).as_long()
            houses[house_num]['HairColor'] = color
        
        for i, sport in enumerate(sports):
            house_num = model.eval(sport_vars[i]).as_long()
            houses[house_num]['FavoriteSport'] = sport
        
        for i, style in enumerate(house_styles):
            house_num = model.eval(house_style_vars[i]).as_long()
            houses[house_num]['HouseStyle'] = style
        
        for i, pet in enumerate(pets):
            house_num = model.eval(pet_vars[i]).as_long()
            houses[house_num]['Pet'] = pet
        
        # Prepare the output in the required JSON format
        header = ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"]
        rows = []
        
        for house_num in sorted(houses.keys()):
            row = [str(house_num)]
            for attr in header[1:]:
                row.append(houses[house_num][attr])
            rows.append(row)
        
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()