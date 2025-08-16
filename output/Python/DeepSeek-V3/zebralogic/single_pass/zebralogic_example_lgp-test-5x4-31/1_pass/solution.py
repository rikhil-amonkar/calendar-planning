import itertools
import json

def solve_puzzle():
    # Define all possible values for each category
    houses = ['1', '2', '3', '4', '5']
    names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']
    
    # Generate all possible permutations for each category
    for name_perm in itertools.permutations(names):
        for vac_perm in itertools.permutations(vacations):
            for child_perm in itertools.permutations(children):
                for nat_perm in itertools.permutations(nationalities):
                    solution = {}
                    valid = True
                    
                    # Create a dictionary for each house
                    for i in range(5):
                        house = str(i+1)
                        solution[house] = {
                            'Name': name_perm[i],
                            'Vacation': vac_perm[i],
                            'Children': child_perm[i],
                            'Nationality': nat_perm[i]
                        }
                    
                    # Check all constraints
                    # 1. The Norwegian is Peter.
                    for house, data in solution.items():
                        if data['Nationality'] == 'norwegian' and data['Name'] != 'Peter':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # 2. The Swedish person is the person's child is named Bella.
                    for house, data in solution.items():
                        if data['Nationality'] == 'swede' and data['Children'] != 'Bella':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # 3. The person who loves beach vacations is directly left of the person's child is named Samantha.
                    beach_left_samantha = False
                    for i in range(1, 5):
                        if solution[str(i)]['Vacation'] == 'beach' and solution[str(i+1)]['Children'] == 'Samantha':
                            beach_left_samantha = True
                            break
                    if not beach_left_samantha:
                        valid = False
                    if not valid:
                        continue
                    
                    # 4. The person's child is named Bella is not in the second house.
                    if solution['2']['Children'] == 'Bella':
                        valid = False
                    if not valid:
                        continue
                    
                    # 5. Alice is the British person.
                    for house, data in solution.items():
                        if data['Name'] == 'Alice' and data['Nationality'] != 'brit':
                            valid = False
                            break
                        if data['Nationality'] == 'brit' and data['Name'] != 'Alice':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # 6. The person who likes going on cruises is in the first house.
                    if solution['1']['Vacation'] != 'cruise':
                        valid = False
                    if not valid:
                        continue
                    
                    # 7. The person's child is named Meredith is in the fourth house.
                    if solution['4']['Children'] != 'Meredith':
                        valid = False
                    if not valid:
                        continue
                    
                    # 8. Eric is not in the fifth house.
                    if solution['5']['Name'] == 'Eric':
                        valid = False
                    if not valid:
                        continue
                    
                    # 9. The Swedish person is somewhere to the right of the Norwegian.
                    norwegian_house = None
                    swede_house = None
                    for house, data in solution.items():
                        if data['Nationality'] == 'norwegian':
                            norwegian_house = int(house)
                        if data['Nationality'] == 'swede':
                            swede_house = int(house)
                    if norwegian_house is None or swede_house is None or swede_house <= norwegian_house:
                        valid = False
                    if not valid:
                        continue
                    
                    # 10. There is one house between the person's child is named Fred and the person who prefers city breaks.
                    fred_house = None
                    city_house = None
                    for house, data in solution.items():
                        if data['Children'] == 'Fred':
                            fred_house = int(house)
                        if data['Vacation'] == 'city':
                            city_house = int(house)
                    if fred_house is None or city_house is None or abs(fred_house - city_house) != 2:
                        valid = False
                    if not valid:
                        continue
                    
                    # 11. Bob is the person who enjoys camping trips.
                    for house, data in solution.items():
                        if data['Name'] == 'Bob' and data['Vacation'] != 'camping':
                            valid = False
                            break
                        if data['Vacation'] == 'camping' and data['Name'] != 'Bob':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # 12. The Dane is in the fifth house.
                    if solution['5']['Nationality'] != 'dane':
                        valid = False
                    if not valid:
                        continue
                    
                    # 13. The person who enjoys camping trips is not in the fifth house.
                    if solution['5']['Vacation'] == 'camping':
                        valid = False
                    if not valid:
                        continue
                    
                    # If all constraints are satisfied, format the solution
                    if valid:
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                                "rows": []
                            }
                        }
                        for house in houses:
                            row = [
                                house,
                                solution[house]['Name'],
                                solution[house]['Vacation'],
                                solution[house]['Children'],
                                solution[house]['Nationality']
                            ]
                            result["solution"]["rows"].append(row)
                        return json.dumps(result, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())