import itertools
import json

# Define the data structures
houses = [{}, {}, {}, {}, {}, {}]  # Six houses
names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
car_models = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

# Direct assignments from clues
def direct_assignments(houses):
    houses[4]['car_model'] = 'ford f150'  # Clue 1
    houses[4]['occupation'] = 'artist' if houses[4].get('occupation') != 'lawyer' else None  # Clue 14
    houses[4]['name'] = 'Arnold' if houses[4].get('name') != 'Peter' else None  # Clue 14
    houses[2]['car_model'] = 'chevrolet silverado' if houses[2].get('car_model') != 'ford f150' else None  # Clue 2
    houses[3]['name'] = 'Eric'  # Clue 7
    houses[3]['occupation'] = 'doctor'  # Clue 7
    houses[5]['name'] = 'Carol' if houses[5].get('name') != 'Eric' else None  # Clue 6
    houses[5]['name'] = None if houses[5].get('name') == 'Peter' else houses[5].get('name')  # Clue 3
    houses[5]['name'] = None if houses[5].get('name') == 'Arnold' else houses[5].get('name')  # Clue 14
    houses[5]['name'] = None if houses[5].get('name') == 'Bob' else houses[5].get('name')  # Clue 10
    houses[5]['name'] = None if houses[5].get('name') == 'Alice' else houses[5].get('name')  # Clue 11
    houses[5]['car_model'] = None if houses[5].get('car_model') == 'toyota camry' else houses[5].get('car_model')  # Clue 11
    houses[5]['car_model'] = None if houses[5].get('car_model') == 'ford f150' else houses[5].get('car_model')  # Clue 1
    houses[5]['car_model'] = None if houses[5].get('car_model') == 'chevrolet silverado' else houses[5].get('car_model')  # Clue 2
    houses[5]['car_model'] = None if houses[5].get('car_model') == 'honda civic' else houses[5].get('car_model')  # Clue 3
    houses[5]['car_model'] = None if houses[5].get('car_model') == 'bmw 3 series' else houses[5].get('car_model')  # Clue 13
    houses[5]['car_model'] = None if houses[5].get('car_model') == 'tesla model 3' else houses[5].get('car_model')  # Clue 13
    houses[4]['occupation'] = None if houses[4].get('occupation') == 'lawyer' else houses[4].get('occupation')  # Clue 4
    houses[4]['occupation'] = None if houses[4].get('occupation') == 'nurse' else houses[4].get('occupation')  # Clue 11
    houses[4]['occupation'] = None if houses[4].get('occupation') == 'engineer' else houses[4].get('occupation')  # Clue 10
    houses[4]['occupation'] = None if houses[4].get('occupation') == 'teacher' else houses[4].get('occupation')  # Clue 8
    houses[4]['occupation'] = 'artist' if houses[4].get('occupation') is None else houses[4].get('occupation')  # Clue 14
    houses[4]['name'] = 'Arnold' if houses[4].get('name') is None else houses[4].get('name')  # Clue 14
    houses[4]['car_model'] = 'ford f150' if houses[4].get('car_model') is None else houses[4].get('car_model')  # Clue 1
    houses[4]['car_model'] = None if houses[4].get('car_model') == 'chevrolet silverado' else houses[4].get('car_model')  # Clue 2
    houses[4]['car_model'] = None if houses[4].get('car_model') == 'honda civic' else houses[4].get('car_model')  # Clue 3
    houses[4]['car_model'] = None if houses[4].get('car_model') == 'toyota camry' else houses[4].get('car_model')  # Clue 11
    houses[4]['car_model'] = None if houses[4].get('car_model') == 'bmw 3 series' else houses[4].get('car_model')  # Clue 13
    houses[4]['car_model'] = None if houses[4].get('car_model') == 'tesla model 3' else houses[4].get('car_model')  # Clue 13
    houses[3]['occupation'] = 'doctor'  # Clue 7
    houses[3]['name'] = 'Eric'  # Clue 7
    houses[0]['occupation'] = 'engineer'  # Clue 10
    houses[0]['name'] = 'Bob'  # Clue 10
    houses[4]['occupation'] = 'artist'  # Clue 14
    houses[4]['name'] = 'Arnold'  # Clue 14

# Function to check if the current assignment is valid
def is_valid(houses):
    # Check clue 3: Honda Civic and Peter are next to each other
    for i in range(5):
        if (houses[i].get('car_model') == 'honda civic' and houses[i + 1].get('name') == 'Peter') or \
           (houses[i].get('name') == 'Peter' and houses[i + 1].get('car_model') == 'honda civic'):
            break
    else:
        return False
    
    # Check clue 5: Nurse is directly left of the artist
    for i in range(5):
        if houses[i].get('occupation') == 'nurse' and houses[i + 1].get('occupation') == 'artist':
            break
    else:
        return False
    
    # Check clue 6: Carol is somewhere to the right of Eric
    if houses.index({'name': 'Eric'}) > houses.index({'name': 'Carol'}):
        return False
    
    # Check clue 8: Eric is a doctor
    if houses[3].get('name') != 'Eric' or houses[3].get('occupation') != 'doctor':
        return False
    
    # Check clue 10: Bob is an engineer
    if houses[0].get('name') != 'Bob' or houses[0].get('occupation') != 'engineer':
        return False
    
    # Check clue 11: Nurse owns a Toyota Camry
    for house in houses:
        if house.get('occupation') == 'nurse' and house.get('car_model') == 'toyota camry':
            break
    else:
        return False
    
    # Check clue 12: One house between Peter and the lawyer
    for i in range(4):
        if (houses[i].get('name') == 'Peter' and houses[i + 2].get('occupation') == 'lawyer') or \
           (houses[i].get('occupation') == 'lawyer' and houses[i + 2].get('name') == 'Peter'):
            break
    else:
        return False
    
    # Check clue 13: One house between Tesla Model 3 and Bob
    for i in range(4):
        if (houses[i].get('car_model') == 'tesla model 3' and houses[i + 2].get('name') == 'Bob') or \
           (houses[i].get('name') == 'Bob' and houses[i + 2].get('car_model') == 'tesla model 3'):
            break
    else:
        return False
    
    # Check clue 14: Arnold is an artist
    for house in houses:
        if house.get('name') == 'Arnold' and house.get('occupation') == 'artist':
            break
    else:
        return False
    
    return True

# Generate all permutations and check for validity
for name_perm in itertools.permutations(names):
    for occupation_perm in itertools.permutations(occupations):
        for car_model_perm in itertools.permutations(car_models):
            for i in range(6):
                houses[i]['name'] = name_perm[i]
                houses[i]['occupation'] = occupation_perm[i]
                houses[i]['car_model'] = car_model_perm[i]
            
            if is_valid(houses):
                break
        else:
            continue
        break
    else:
        continue
    break

# Prepare the output in JSON format
output = {
    "solution": {
        "header": ["House", "Name", "Occupation", "CarModel"],
        "rows": []
    }
}

for i, house in enumerate(houses, start=1):
    output["solution"]["rows"].append([str(i), house['name'], house['occupation'], house['car_model']])

print(json.dumps(output, indent=2))