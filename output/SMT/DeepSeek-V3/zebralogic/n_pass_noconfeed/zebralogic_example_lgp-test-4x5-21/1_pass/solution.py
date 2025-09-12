import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define the attributes
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    sports = ['soccer', 'tennis', 'basketball', 'swimming']
    cars = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
    flowers = ['daffodils', 'roses', 'lilies', 'carnations']
    
    # Create integer variables for each attribute's house position
    name_vars = [Int(f'name_{n}') for n in names]
    smoothie_vars = [Int(f'smoothie_{s}') for s in smoothies]
    sport_vars = [Int(f'sport_{sp}') for sp in sports]
    car_vars = [Int(f'car_{c}') for c in cars]
    flower_vars = [Int(f'flower_{f}') for f in flowers]
    
    # All attributes must be in houses 1-4
    for var in name_vars + smoothie_vars + sport_vars + car_vars + flower_vars:
        s.add(And(var >= 1, var <= 4))
    
    # All attributes of the same type must be distinct
    s.add(Distinct(name_vars))
    s.add(Distinct(smoothie_vars))
    s.add(Distinct(sport_vars))
    s.add(Distinct(car_vars))
    s.add(Distinct(flower_vars))
    
    # Clue 1: The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
    s.add(car_vars[cars.index('tesla model 3')] == flower_vars[flowers.index('roses')])
    
    # Clue 2: Peter is the Dragonfruit smoothie lover.
    s.add(name_vars[names.index('Peter')] == smoothie_vars[smoothies.index('dragonfruit')])
    
    # Clue 3: The Desert smoothie lover is the person who owns a Toyota Camry.
    s.add(smoothie_vars[smoothies.index('desert')] == car_vars[cars.index('toyota camry')])
    
    # Clue 4: The person who loves tennis is in the first house.
    s.add(sport_vars[sports.index('tennis')] == 1)
    
    # Clue 5: The person who owns a Toyota Camry and the person who loves basketball are next to each other.
    toyota_camry_house = car_vars[cars.index('toyota camry')]
    basketball_house = sport_vars[sports.index('basketball')]
    s.add(Or(
        toyota_camry_house == basketball_house + 1,
        toyota_camry_house == basketball_house - 1
    ))
    
    # Clue 6: Arnold is the person who loves basketball.
    s.add(name_vars[names.index('Arnold')] == sport_vars[sports.index('basketball')])
    
    # Clue 7: The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
    s.add(car_vars[cars.index('honda civic')] == flower_vars[flowers.index('daffodils')])
    
    # Clue 8: Eric is the person who loves the rose bouquet.
    s.add(name_vars[names.index('Eric')] == flower_vars[flowers.index('roses')])
    
    # Clue 9: The Watermelon smoothie lover is not in the first house.
    s.add(smoothie_vars[smoothies.index('watermelon')] != 1)
    
    # Clue 10: The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
    honda_civic_house = car_vars[cars.index('honda civic')]
    desert_smoothie_house = smoothie_vars[smoothies.index('desert')]
    s.add(honda_civic_house > desert_smoothie_house)
    
    # Clue 11: The person who loves basketball is the person who loves the bouquet of lilies.
    s.add(sport_vars[sports.index('basketball')] == flower_vars[flowers.index('lilies')])
    
    # Clue 12: The person who loves tennis and the person who loves soccer are next to each other.
    tennis_house = sport_vars[sports.index('tennis')]
    soccer_house = sport_vars[sports.index('soccer')]
    s.add(Or(
        tennis_house == soccer_house + 1,
        tennis_house == soccer_house - 1
    ))
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                "rows": [[], [], [], []]
            }
        }
        
        # For each house, find the attributes
        for house in range(1, 5):
            # Find name for this house
            for i, var in enumerate(name_vars):
                if model.evaluate(var).as_long() == house:
                    name = names[i]
                    break
            
            # Find smoothie for this house
            for i, var in enumerate(smoothie_vars):
                if model.evaluate(var).as_long() == house:
                    smoothie = smoothies[i]
                    break
            
            # Find sport for this house
            for i, var in enumerate(sport_vars):
                if model.evaluate(var).as_long() == house:
                    sport = sports[i]
                    break
            
            # Find car for this house
            for i, var in enumerate(car_vars):
                if model.evaluate(var).as_long() == house:
                    car = cars[i]
                    break
            
            # Find flower for this house
            for i, var in enumerate(flower_vars):
                if model.evaluate(var).as_long() == house:
                    flower = flowers[i]
                    break
            
            # Add row to result
            result["solution"]["rows"][house-1] = [str(house), name, smoothie, sport, car, flower]
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()