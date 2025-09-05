import json
from z3 import *

def main():
    # Define the attributes and their integer mappings
    names = {"Peter": 1, "Arnold": 2, "Eric": 3, "Alice": 4}
    flowers = {"daffodils": 1, "carnations": 2, "roses": 3, "lilies": 4}
    heights = {"very short": 1, "short": 2, "tall": 3, "average": 4}
    mothers = {"Janelle": 1, "Kailyn": 2, "Holly": 3, "Aniya": 4}
    occupations = {"engineer": 1, "doctor": 2, "teacher": 3, "artist": 4}
    sports = {"swimming": 1, "basketball": 2, "tennis": 3, "soccer": 4}
    
    # Reverse mappings for output
    rev_names = {v: k for k, v in names.items()}
    rev_flowers = {v: k for k, v in flowers.items()}
    rev_heights = {v: k for k, v in heights.items()}
    rev_mothers = {v: k for k, v in mothers.items()}
    rev_occupations = {v: k for k, v in occupations.items()}
    rev_sports = {v: k for k, v in sports.items()}
    
    # Create solver
    solver = Solver()
    
    # Define variables for each house and attribute
    house_vars = {}
    for house in range(1, 5):
        house_vars[house] = {
            'name': Int(f'name_{house}'),
            'flower': Int(f'flower_{house}'),
            'height': Int(f'height_{house}'),
            'mother': Int(f'mother_{house}'),
            'occupation': Int(f'occupation_{house}'),
            'sport': Int(f'sport_{house}')
        }
    
    # Add constraints: each attribute must be between 1 and 4
    for house in range(1, 5):
        for attr in house_vars[house].values():
            solver.add(And(attr >= 1, attr <= 4))
    
    # Add constraints: all attributes must have distinct values within their category
    for attr_name in ['name', 'flower', 'height', 'mother', 'occupation', 'sport']:
        solver.add(Distinct([house_vars[h][attr_name] for h in range(1, 5)]))
    
    # Clue 1: The person who loves swimming is the person who loves the rose bouquet.
    for h in range(1, 5):
        solver.add(
            (house_vars[h]['sport'] == sports['swimming']) == 
            (house_vars[h]['flower'] == flowers['roses'])
        )
    
    # Clue 2: The person who loves the rose bouquet is Eric.
    for h in range(1, 5):
        solver.add(
            (house_vars[h]['flower'] == flowers['roses']) == 
            (house_vars[h]['name'] == names['Eric'])
        )
    
    # Clue 3: Arnold is the person who is tall.
    for h in range(1, 5):
        solver.add(
            (house_vars[h]['name'] == names['Arnold']) == 
            (house_vars[h]['height'] == heights['tall'])
        )
    
    # Clue 4: The person who loves daffodils is right of the engineer.
    engineer_house = Int('engineer_house')
    solver.add(engineer_house >= 1, engineer_house <= 4)
    solver.add(Or([And(house_vars[h]['occupation'] == occupations['engineer'], engineer_house == h) for h in range(1, 5)]))
    
    daffodils_house = Int('daffodils_house')
    solver.add(daffodils_house >= 1, daffodils_house <= 4)
    solver.add(Or([And(house_vars[h]['flower'] == flowers['daffodils'], daffodils_house == h) for h in range(1, 5)]))
    
    solver.add(daffodils_house > engineer_house)
    
    # Clue 5: The person who loves soccer is the person who is short.
    for h in range(1, 5):
        solver.add(
            (house_vars[h]['sport'] == sports['soccer']) == 
            (house_vars[h]['height'] == heights['short'])
        )
    
    # Clue 6: The teacher is in the first house.
    solver.add(house_vars[1]['occupation'] == occupations['teacher'])
    
    # Clue 7: The person with mother Janelle loves carnations.
    for h in range(1, 5):
        solver.add(
            (house_vars[h]['mother'] == mothers['Janelle']) == 
            (house_vars[h]['flower'] == flowers['carnations'])
        )
    
    # Clue 8: The person who loves basketball has average height.
    for h in range(1, 5):
        solver.add(
            (house_vars[h]['sport'] == sports['basketball']) == 
            (house_vars[h]['height'] == heights['average'])
        )
    
    # Clue 9: Arnold is not in the third house.
    solver.add(house_vars[3]['name'] != names['Arnold'])
    
    # Clue 10: The person with mother Holly is right of the person with average height.
    avg_height_house = Int('avg_height_house')
    solver.add(avg_height_house >= 1, avg_height_house <= 4)
    solver.add(Or([And(house_vars[h]['height'] == heights['average'], avg_height_house == h) for h in range(1, 5)]))
    
    holly_house = Int('holly_house')
    solver.add(holly_house >= 1, holly_house <= 4)
    solver.add(Or([And(house_vars[h]['mother'] == mothers['Holly'], holly_house == h) for h in range(1, 5)]))
    
    solver.add(holly_house > avg_height_house)
    
    # Clue 11: Peter is the doctor.
    for h in range(1, 5):
        solver.add(
            (house_vars[h]['name'] == names['Peter']) == 
            (house_vars[h]['occupation'] == occupations['doctor'])
        )
    
    # Clue 12: The person with mother Aniya is Alice.
    for h in range(1, 5):
        solver.add(
            (house_vars[h]['mother'] == mothers['Aniya']) == 
            (house_vars[h]['name'] == names['Alice'])
        )
    
    # Clue 13: Arnold loves lilies.
    for h in range(1, 5):
        solver.add(
            (house_vars[h]['name'] == names['Arnold']) == 
            (house_vars[h]['flower'] == flowers['lilies'])
        )
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                "rows": []
            }
        }
        
        for house in range(1, 5):
            row = [str(house)]
            # Name
            name_val = model[house_vars[house]['name']].as_long()
            row.append(rev_names[name_val])
            # Flower
            flower_val = model[house_vars[house]['flower']].as_long()
            row.append(rev_flowers[flower_val])
            # Height
            height_val = model[house_vars[house]['height']].as_long()
            row.append(rev_heights[height_val])
            # Mother
            mother_val = model[house_vars[house]['mother']].as_long()
            row.append(rev_mothers[mother_val])
            # Occupation
            occupation_val = model[house_vars[house]['occupation']].as_long()
            row.append(rev_occupations[occupation_val])
            # FavoriteSport
            sport_val = model[house_vars[house]['sport']].as_long()
            row.append(rev_sports[sport_val])
            
            solution["solution"]["rows"].append(row)
        
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()