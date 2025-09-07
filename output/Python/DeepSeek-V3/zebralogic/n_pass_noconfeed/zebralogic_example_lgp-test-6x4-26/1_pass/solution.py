import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Peter', 'Bob', 'Carol', 'Eric', 'Alice', 'Arnold']
    pets = ['bird', 'dog', 'cat', 'rabbit', 'fish', 'hamster']
    house_styles = ['victorian', 'ranch', 'modern', 'mediterranean', 'colonial', 'craftsman']
    birthdays = ['jan', 'feb', 'mar', 'april', 'may', 'sept']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for pet_perm in permutations(pets):
            for style_perm in permutations(house_styles):
                for bday_perm in permutations(birthdays):
                    # Create assignment dictionaries
                    assignment = {}
                    for i, house in enumerate(houses):
                        assignment[house] = {
                            'name': name_perm[i],
                            'pet': pet_perm[i],
                            'style': style_perm[i],
                            'bday': bday_perm[i]
                        }
                    
                    # Check all constraints
                    # Clue 3: The person whose birthday is in May is in the second house.
                    if assignment[2]['bday'] != 'may':
                        continue
                    
                    # Clue 4: The person living in a colonial-style house is in the second house.
                    if assignment[2]['style'] != 'colonial':
                        continue
                    
                    # Clue 5: Carol is in the third house.
                    if assignment[3]['name'] != 'Carol':
                        continue
                    
                    # Clue 6: The person in a Mediterranean-style villa is not in the sixth house.
                    if assignment[6]['style'] == 'mediterranean':
                        continue
                    
                    # Clue 8: Eric is in the sixth house.
                    if assignment[6]['name'] != 'Eric':
                        continue
                    
                    # Clue 11: The person in a Craftsman-style house is Arnold.
                    craftsman_house = None
                    for house in houses:
                        if assignment[house]['style'] == 'craftsman':
                            craftsman_house = house
                            break
                    if craftsman_house is None or assignment[craftsman_house]['name'] != 'Arnold':
                        continue
                    
                    # Clue 14: Peter is the person living in a colonial-style house.
                    colonial_house = None
                    for house in houses:
                        if assignment[house]['style'] == 'colonial':
                            colonial_house = house
                            break
                    if colonial_house is None or assignment[colonial_house]['name'] != 'Peter':
                        continue
                    
                    # Clue 17: Carol is the person whose birthday is in March.
                    if assignment[3]['bday'] != 'mar':
                        continue
                    
                    # Clue 18: The person in a Craftsman-style house is in the fourth house.
                    if craftsman_house != 4:
                        continue
                    
                    # Clue 19: The person who owns a dog is in the fourth house.
                    if assignment[4]['pet'] != 'dog':
                        continue
                    
                    # Clue 1: The person with a pet hamster is somewhere to the right of the person whose birthday is in March.
                    hamster_house = None
                    mar_bday_house = None
                    for house in houses:
                        if assignment[house]['pet'] == 'hamster':
                            hamster_house = house
                        if assignment[house]['bday'] == 'mar':
                            mar_bday_house = house
                    if hamster_house is None or mar_bday_house is None or hamster_house <= mar_bday_house:
                        continue
                    
                    # Clue 2: The person whose birthday is in January is somewhere to the left of the person whose birthday is in September.
                    jan_bday_house = None
                    sept_bday_house = None
                    for house in houses:
                        if assignment[house]['bday'] == 'jan':
                            jan_bday_house = house
                        if assignment[house]['bday'] == 'sept':
                            sept_bday_house = house
                    if jan_bday_house is None or sept_bday_house is None or jan_bday_house >= sept_bday_house:
                        continue
                    
                    # Clue 7: The person with an aquarium of fish is somewhere to the right of Bob.
                    fish_house = None
                    bob_house = None
                    for house in houses:
                        if assignment[house]['pet'] == 'fish':
                            fish_house = house
                        if assignment[house]['name'] == 'Bob':
                            bob_house = house
                    if fish_house is None or bob_house is None or fish_house <= bob_house:
                        continue
                    
                    # Clue 9: There is one house between the person who has a cat and the person residing in a Victorian house.
                    cat_house = None
                    victorian_house = None
                    for house in houses:
                        if assignment[house]['pet'] == 'cat':
                            cat_house = house
                        if assignment[house]['style'] == 'victorian':
                            victorian_house = house
                    if cat_house is None or victorian_house is None or abs(cat_house - victorian_house) != 2:
                        continue
                    
                    # Clue 10: There are two houses between the person residing in a Victorian house and the person with a pet hamster.
                    if victorian_house is None or hamster_house is None or abs(victorian_house - hamster_house) != 3:
                        continue
                    
                    # Clue 12: The person living in a colonial-style house is somewhere to the left of the person in a modern-style house.
                    modern_house = None
                    for house in houses:
                        if assignment[house]['style'] == 'modern':
                            modern_house = house
                            break
                    if modern_house is None or colonial_house >= modern_house:
                        continue
                    
                    # Clue 13: The person with an aquarium of fish is not in the second house.
                    if fish_house == 2:
                        continue
                    
                    # Clue 15: The person whose birthday is in January is directly left of the person whose birthday is in April.
                    april_bday_house = None
                    for house in houses:
                        if assignment[house]['bday'] == 'april':
                            april_bday_house = house
                            break
                    if jan_bday_house is None or april_bday_house is None or april_bday_house - jan_bday_house != 1:
                        continue
                    
                    # Clue 16: There is one house between the person who keeps a pet bird and the person in a modern-style house.
                    bird_house = None
                    for house in houses:
                        if assignment[house]['pet'] == 'bird':
                            bird_house = house
                            break
                    if bird_house is None or modern_house is None or abs(bird_house - modern_house) != 2:
                        continue
                    
                    # If we reach here, all constraints are satisfied
                    result = {
                        "solution": {
                            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        row = [
                            str(house),
                            assignment[house]['name'],
                            assignment[house]['pet'],
                            assignment[house]['style'],
                            assignment[house]['bday']
                        ]
                        result["solution"]["rows"].append(row)
                    
                    print(json.dumps(result, indent=2))
                    return
    
    print('{"solution": {"header": ["House", "Name", "Pet", "HouseStyle", "Birthday"], "rows": []}}')

if __name__ == "__main__":
    main()