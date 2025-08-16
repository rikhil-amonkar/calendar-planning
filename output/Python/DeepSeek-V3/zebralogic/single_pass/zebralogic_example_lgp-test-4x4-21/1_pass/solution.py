import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Alice', 'Arnold']
    car_models = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
    birthday_months = ['jan', 'april', 'sept', 'feb']
    hobbies = ['painting', 'cooking', 'gardening', 'photography']
    
    # We'll represent each house as a dictionary with keys: name, car_model, birthday, hobby
    # Initialize all possibilities
    houses = [{'name': None, 'car_model': None, 'birthday': None, 'hobby': None} for _ in range(4)]
    
    # Apply clue 11: Peter's birthday is jan
    for i in range(4):
        if houses[i]['name'] is None:
            houses[i]['name'] = 'Peter'
            houses[i]['birthday'] = 'jan'
            break
    
    # Apply clue 1: jan is not in house 2
    if houses[1]['birthday'] == 'jan':
        # Move Peter to another house
        for i in [0, 2, 3]:
            if houses[i]['name'] is None:
                houses[i]['name'] = 'Peter'
                houses[i]['birthday'] = 'jan'
                houses[1]['name'] = None
                houses[1]['birthday'] = None
                break
    
    # Apply clue 8: Peter owns toyota camry
    for i in range(4):
        if houses[i]['name'] == 'Peter':
            houses[i]['car_model'] = 'toyota camry'
            break
    
    # Apply clue 6: Arnold owns tesla model 3
    for i in range(4):
        if houses[i]['name'] == 'Arnold':
            houses[i]['car_model'] = 'tesla model 3'
            break
    
    # Apply clue 9: Arnold's birthday is april
    for i in range(4):
        if houses[i]['name'] == 'Arnold':
            houses[i]['birthday'] = 'april'
            break
    
    # Apply clue 4: honda civic is directly left of tesla model 3
    for i in range(3):
        if houses[i+1]['car_model'] == 'tesla model 3':
            houses[i]['car_model'] = 'honda civic'
            break
    
    # Apply clue 5: one house between tesla model 3 and gardening
    # Find tesla model 3 position
    tesla_pos = None
    for i in range(4):
        if houses[i]['car_model'] == 'tesla model 3':
            tesla_pos = i
            break
    if tesla_pos is not None:
        gardening_pos = tesla_pos + 2
        if gardening_pos < 4:
            houses[gardening_pos]['hobby'] = 'gardening'
    
    # Apply clue 10: Alice is photography enthusiast
    for i in range(4):
        if houses[i]['name'] == 'Alice':
            houses[i]['hobby'] = 'photography'
            break
    
    # Apply clue 2 and 3: photography is left of Eric and Peter
    # Since Peter is already placed, we need to find photography position
    photography_pos = None
    for i in range(4):
        if houses[i]['hobby'] == 'photography':
            photography_pos = i
            break
    if photography_pos is not None:
        # Eric must be to the right of photography
        for i in range(photography_pos + 1, 4):
            if houses[i]['name'] is None:
                houses[i]['name'] = 'Eric'
                break
    
    # Apply clue 7: feb birthday is cooking
    for i in range(4):
        if houses[i]['birthday'] == 'feb':
            houses[i]['hobby'] = 'cooking'
            break
    
    # Fill in remaining names
    for i in range(4):
        if houses[i]['name'] is None:
            for name in names:
                if name not in [h['name'] for h in houses if h['name'] is not None]:
                    houses[i]['name'] = name
                    break
    
    # Fill in remaining car models
    for i in range(4):
        if houses[i]['car_model'] is None:
            for car in car_models:
                if car not in [h['car_model'] for h in houses if h['car_model'] is not None]:
                    houses[i]['car_model'] = car
                    break
    
    # Fill in remaining birthdays
    for i in range(4):
        if houses[i]['birthday'] is None:
            for bday in birthday_months:
                if bday not in [h['birthday'] for h in houses if h['birthday'] is not None]:
                    houses[i]['birthday'] = bday
                    break
    
    # Fill in remaining hobbies
    for i in range(4):
        if houses[i]['hobby'] is None:
            for hobby in hobbies:
                if hobby not in [h['hobby'] for h in houses if h['hobby'] is not None]:
                    houses[i]['hobby'] = hobby
                    break
    
    # Prepare the output
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
            "rows": []
        }
    }
    
    for i in range(4):
        house = houses[i]
        solution["solution"]["rows"].append([
            str(i+1),
            house['name'],
            house['car_model'],
            house['birthday'],
            house['hobby']
        ])
    
    return json.dumps(solution)

print(solve_puzzle())