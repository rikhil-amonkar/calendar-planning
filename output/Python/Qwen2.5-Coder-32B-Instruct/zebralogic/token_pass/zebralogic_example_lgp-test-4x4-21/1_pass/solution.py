import itertools
import json

# Initialize possible values for each attribute
names = ['Eric', 'Peter', 'Alice', 'Arnold']
car_models = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
birthdays = ['jan', 'april', 'sept', 'feb']
hobbies = ['painting', 'cooking', 'gardening', 'photography']

# Create a list of houses with possible attributes
houses = [{'name': set(names), 'car_model': set(car_models), 'birthday': set(birthdays), 'hobby': set(hobbies)} for _ in range(4)]

# Apply direct assignments from clues
# Clue 6: The person who owns a Tesla Model 3 is Arnold.
houses[0]['name'].discard('Arnold')  # Assuming Arnold is in the first house initially, we'll adjust later
houses[1]['name'].discard('Arnold')
houses[2]['name'].discard('Arnold')
houses[3]['name'].discard('Arnold')
for house in houses:
    house['car_model'].discard('tesla model 3')

# Clue 8: The person who owns a Toyota Camry is Peter.
houses[0]['name'].discard('Peter')  # Assuming Peter is in the first house initially, we'll adjust later
houses[1]['name'].discard('Peter')
houses[2]['name'].discard('Peter')
houses[3]['name'].discard('Peter')
for house in houses:
    house['car_model'].discard('toyota camry')

# Clue 10: Alice is the photography enthusiast.
houses[0]['name'].discard('Alice')  # Assuming Alice is in the first house initially, we'll adjust later
houses[1]['name'].discard('Alice')
houses[2]['name'].discard('Alice')
houses[3]['name'].discard('Alice')
for house in houses:
    house['hobby'].discard('photography')

# Clue 11: Peter is the person whose birthday is in January.
houses[0]['name'].discard('Peter')  # Assuming Peter is in the first house initially, we'll adjust later
houses[1]['name'].discard('Peter')
houses[2]['name'].discard('Peter')
houses[3]['name'].discard('Peter')
for house in houses:
    house['birthday'].discard('jan')

# Clue 7: The person whose birthday is in February is the person who loves cooking.
houses[0]['birthday'].discard('feb')  # Assuming Feb is in the first house initially, we'll adjust later
houses[1]['birthday'].discard('feb')
houses[2]['birthday'].discard('feb')
houses[3]['birthday'].discard('feb')
for house in houses:
    house['hobby'].discard('cooking')

# Clue 9: The person whose birthday is in April is Arnold.
houses[0]['birthday'].discard('april')  # Assuming April is in the first house initially, we'll adjust later
houses[1]['birthday'].discard('april')
houses[2]['birthday'].discard('april')
houses[3]['birthday'].discard('april')
for house in houses:
    house['name'].discard('Arnold')

# Now, let's use positional clues and process of elimination to find the correct arrangement
def check_solution(houses):
    # Clue 1: The person whose birthday is in January is not in the second house.
    if 'jan' in houses[1]['birthday']:
        return False
    
    # Clue 2 & 3: The photography enthusiast is somewhere to the left of Eric and Peter.
    photo_index = None
    eric_index = None
    peter_index = None
    for i, house in enumerate(houses):
        if 'photography' in house['hobby']:
            photo_index = i
        if 'Eric' in house['name']:
            eric_index = i
        if 'Peter' in house['name']:
            peter_index = i
    if photo_index is not None and (eric_index is None or peter_index is None):
        return False
    if photo_index is not None and (eric_index is not None and photo_index >= eric_index):
        return False
    if photo_index is not None and (peter_index is not None and photo_index >= peter_index):
        return False
    
    # Clue 4: The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
    honda_index = None
    tesla_index = None
    for i, house in enumerate(houses):
        if 'honda civic' in house['car_model']:
            honda_index = i
        if 'tesla model 3' in house['car_model']:
            tesla_index = i
    if honda_index is not None and tesla_index is not None and honda_index + 1 != tesla_index:
        return False
    
    # Clue 5: There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
    gardening_index = None
    for i, house in enumerate(houses):
        if 'gardening' in house['hobby']:
            gardening_index = i
    if tesla_index is not None and gardening_index is not None and abs(tesla_index - gardening_index) != 2:
        return False
    
    # Clue 7: The person whose birthday is in February is the person who loves cooking.
    feb_index = None
    cooking_index = None
    for i, house in enumerate(houses):
        if 'feb' in house['birthday']:
            feb_index = i
        if 'cooking' in house['hobby']:
            cooking_index = i
    if feb_index is not None and cooking_index is not None and feb_index != cooking_index:
        return False
    
    # Clue 9: The person whose birthday is in April is Arnold.
    april_index = None
    arnold_index = None
    for i, house in enumerate(houses):
        if 'april' in house['birthday']:
            april_index = i
        if 'Arnold' in house['name']:
            arnold_index = i
    if april_index is not None and arnold_index is not None and april_index != arnold_index:
        return False
    
    # Clue 10: Alice is the photography enthusiast.
    alice_index = None
    for i, house in enumerate(houses):
        if 'Alice' in house['name']:
            alice_index = i
    if alice_index is not None and photo_index is not None and alice_index != photo_index:
        return False
    
    # Clue 11: Peter is the person whose birthday is in January.
    jan_index = None
    for i, house in enumerate(houses):
        if 'jan' in house['birthday']:
            jan_index = i
    if jan_index is not None and peter_index is not None and jan_index != peter_index:
        return False
    
    return True

# Generate all permutations and check each one
for perm in itertools.permutations(range(4)):
    # Assign names
    for i, index in enumerate(perm):
        houses[index]['name'] = {names[i]}
    
    # Assign car models
    car_perm = list(itertools.permutations(car_models))
    for car_p in car_perm:
        for i, car in enumerate(car_p):
            houses[i]['car_model'] = {car}
        
        # Assign birthdays
        birthday_perm = list(itertools.permutations(birthdays))
        for birthday_p in birthday_perm:
            for i, birthday in enumerate(birthday_p):
                houses[i]['birthday'] = {birthday}
            
            # Assign hobbies
            hobby_perm = list(itertools.permutations(hobbies))
            for hobby_p in hobby_perm:
                for i, hobby in enumerate(hobby_p):
                    houses[i]['hobby'] = {hobby}
                
                if check_solution(houses):
                    # If the solution is valid, format the output
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                            "rows": []
                        }
                    }
                    for i, house in enumerate(houses):
                        solution["solution"]["rows"].append([
                            str(i + 1),
                            next(iter(house['name'])),
                            next(iter(house['car_model'])),
                            next(iter(house['birthday'])),
                            next(iter(house['hobby']))
                        ])
                    
                    print(json.dumps(solution, indent=2))
                    exit()