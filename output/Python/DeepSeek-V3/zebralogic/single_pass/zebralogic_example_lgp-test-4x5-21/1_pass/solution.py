import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    sports = ['soccer', 'tennis', 'basketball', 'swimming']
    cars = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
    flowers = ['daffodils', 'roses', 'lilies', 'carnations']
    
    # Generate all possible permutations for each category
    for name_order in permutations(names):
        for smoothie_order in permutations(smoothies):
            for sport_order in permutations(sports):
                for car_order in permutations(cars):
                    for flower_order in permutations(flowers):
                        # Assign to houses 1-4
                        solution = {
                            1: {
                                'Name': name_order[0],
                                'Smoothie': smoothie_order[0],
                                'FavoriteSport': sport_order[0],
                                'CarModel': car_order[0],
                                'Flower': flower_order[0]
                            },
                            2: {
                                'Name': name_order[1],
                                'Smoothie': smoothie_order[1],
                                'FavoriteSport': sport_order[1],
                                'CarModel': car_order[1],
                                'Flower': flower_order[1]
                            },
                            3: {
                                'Name': name_order[2],
                                'Smoothie': smoothie_order[2],
                                'FavoriteSport': sport_order[2],
                                'CarModel': car_order[2],
                                'Flower': flower_order[2]
                            },
                            4: {
                                'Name': name_order[3],
                                'Smoothie': smoothie_order[3],
                                'FavoriteSport': sport_order[3],
                                'CarModel': car_order[3],
                                'Flower': flower_order[3]
                            }
                        }
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 2: Peter is the Dragonfruit smoothie lover.
                        peter_house = None
                        for house in solution:
                            if solution[house]['Name'] == 'Peter':
                                peter_house = house
                                break
                        if peter_house is None or solution[peter_house]['Smoothie'] != 'dragonfruit':
                            valid = False
                            continue
                        
                        # Clue 4: The person who loves tennis is in the first house.
                        if solution[1]['FavoriteSport'] != 'tennis':
                            valid = False
                            continue
                        
                        # Clue 6: Arnold is the person who loves basketball.
                        arnold_house = None
                        for house in solution:
                            if solution[house]['Name'] == 'Arnold':
                                arnold_house = house
                                break
                        if arnold_house is None or solution[arnold_house]['FavoriteSport'] != 'basketball':
                            valid = False
                            continue
                        
                        # Clue 11: The person who loves basketball is the person who loves the bouquet of lilies.
                        if solution[arnold_house]['Flower'] != 'lilies':
                            valid = False
                            continue
                        
                        # Clue 8: Eric is the person who loves the rose bouquet.
                        eric_house = None
                        for house in solution:
                            if solution[house]['Name'] == 'Eric':
                                eric_house = house
                                break
                        if eric_house is None or solution[eric_house]['Flower'] != 'roses':
                            valid = False
                            continue
                        
                        # Clue 1: The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
                        tesla_house = None
                        for house in solution:
                            if solution[house]['CarModel'] == 'tesla model 3':
                                tesla_house = house
                                break
                        if tesla_house is None or solution[tesla_house]['Flower'] != 'roses':
                            valid = False
                            continue
                        if tesla_house != eric_house:
                            valid = False
                            continue
                        
                        # Clue 3: The Desert smoothie lover is the person who owns a Toyota Camry.
                        desert_house = None
                        for house in solution:
                            if solution[house]['Smoothie'] == 'desert':
                                desert_house = house
                                break
                        if desert_house is None or solution[desert_house]['CarModel'] != 'toyota camry':
                            valid = False
                            continue
                        
                        # Clue 5: The person who owns a Toyota Camry and the person who loves basketball are next to each other.
                        if abs(desert_house - arnold_house) != 1:
                            valid = False
                            continue
                        
                        # Clue 7: The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
                        honda_house = None
                        for house in solution:
                            if solution[house]['CarModel'] == 'honda civic':
                                honda_house = house
                                break
                        if honda_house is None or solution[honda_house]['Flower'] != 'daffodils':
                            valid = False
                            continue
                        
                        # Clue 10: The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
                        if honda_house <= desert_house:
                            valid = False
                            continue
                        
                        # Clue 9: The Watermelon smoothie lover is not in the first house.
                        watermelon_house = None
                        for house in solution:
                            if solution[house]['Smoothie'] == 'watermelon':
                                watermelon_house = house
                                break
                        if watermelon_house == 1:
                            valid = False
                            continue
                        
                        # Clue 12: The person who loves tennis and the person who loves soccer are next to each other.
                        soccer_house = None
                        for house in solution:
                            if solution[house]['FavoriteSport'] == 'soccer':
                                soccer_house = house
                                break
                        if soccer_house is None or abs(soccer_house - 1) != 1:
                            valid = False
                            continue
                        
                        if valid:
                            # Prepare the output
                            output = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                                    "rows": []
                                }
                            }
                            for house in sorted(solution.keys()):
                                row = [
                                    str(house),
                                    solution[house]['Name'],
                                    solution[house]['Smoothie'] if 'Smoothie' not in solution[house] else solution[house]['Smoothie'],
                                    solution[house]['FavoriteSport'],
                                    solution[house]['CarModel'],
                                    solution[house]['Flower']
                                ]
                                output["solution"]["rows"].append(row)
                            return output
    return {"solution": {"header": [], "rows": []}}

result = solve_puzzle()
print(json.dumps(result, indent=2))