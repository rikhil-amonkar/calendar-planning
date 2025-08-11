import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Eric', 'Peter', 'Alice', 'Arnold']
    cars = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
    months = ['jan', 'april', 'sept', 'feb']
    hobbies = ['painting', 'cooking', 'gardening', 'photography']
    
    # Generate all possible permutations for each attribute
    for name_order in permutations(names):
        for car_order in permutations(cars):
            for month_order in permutations(months):
                for hobby_order in permutations(hobbies):
                    # Create a list of houses with their attributes
                    houses = [
                        {
                            'House': str(i + 1),
                            'Name': name_order[i],
                            'car': car_order[i],
                            'birthday month': month_order[i],
                            'hobby': hobby_order[i]
                        }
                        for i in range(4)
                    ]
                    
                    # Check all constraints
                    valid = True
                    
                    # Constraint 1: jan is not in house 2
                    if any(house['birthday month'] == 'jan' and house['House'] == '2' for house in houses):
                        valid = False
                    
                    # Constraint 2: photography is left of Eric
                    if valid:
                        photo_pos = None
                        eric_pos = None
                        for house in houses:
                            if house['hobby'] == 'photography':
                                photo_pos = int(house['House'])
                            if house['Name'] == 'Eric':
                                eric_pos = int(house['House'])
                        if photo_pos is None or eric_pos is None or photo_pos >= eric_pos:
                            valid = False
                    
                    # Constraint 3: photography is left of Peter
                    if valid:
                        peter_pos = None
                        for house in houses:
                            if house['Name'] == 'Peter':
                                peter_pos = int(house['House'])
                        if photo_pos is None or peter_pos is None or photo_pos >= peter_pos:
                            valid = False
                    
                    # Constraint 4: honda civic is directly left of tesla model 3
                    if valid:
                        honda_pos = None
                        tesla_pos = None
                        for house in houses:
                            if house['car'] == 'honda civic':
                                honda_pos = int(house['House'])
                            if house['car'] == 'tesla model 3':
                                tesla_pos = int(house['House'])
                        if honda_pos is None or tesla_pos is None or honda_pos + 1 != tesla_pos:
                            valid = False
                    
                    # Constraint 5: one house between tesla and gardening
                    if valid:
                        gardening_pos = None
                        for house in houses:
                            if house['hobby'] == 'gardening':
                                gardening_pos = int(house['House'])
                        if gardening_pos is None or abs(tesla_pos - gardening_pos) != 2:
                            valid = False
                    
                    # Constraint 6: tesla owner is Arnold
                    if valid:
                        for house in houses:
                            if house['car'] == 'tesla model 3' and house['Name'] != 'Arnold':
                                valid = False
                                break
                    
                    # Constraint 7: feb birthday loves cooking
                    if valid:
                        for house in houses:
                            if house['birthday month'] == 'feb' and house['hobby'] != 'cooking':
                                valid = False
                                break
                    
                    # Constraint 8: toyota camry is Peter
                    if valid:
                        for house in houses:
                            if house['car'] == 'toyota camry' and house['Name'] != 'Peter':
                                valid = False
                                break
                    
                    # Constraint 9: april birthday is Arnold
                    if valid:
                        for house in houses:
                            if house['birthday month'] == 'april' and house['Name'] != 'Arnold':
                                valid = False
                                break
                    
                    # Constraint 10: Alice is photography enthusiast
                    if valid:
                        for house in houses:
                            if house['Name'] == 'Alice' and house['hobby'] != 'photography':
                                valid = False
                                break
                    
                    # Constraint 11: Peter's birthday is jan
                    if valid:
                        for house in houses:
                            if house['Name'] == 'Peter' and house['birthday month'] != 'jan':
                                valid = False
                                break
                    
                    if valid:
                        # Prepare the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "car", "birthday month", "hobby"],
                                "rows": [
                                    [house['House'], house['Name'], house['car'], house['birthday month'], house['hobby']]
                                    for house in houses
                                ]
                            }
                        }
                        return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())