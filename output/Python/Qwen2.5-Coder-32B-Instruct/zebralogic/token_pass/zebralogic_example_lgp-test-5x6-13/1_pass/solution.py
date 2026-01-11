import json

# Define the domains for each attribute
names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
foods = ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza']
car_models = ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic']
phone_models = ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50']
occupations = ['teacher', 'lawyer', 'doctor', 'artist', 'engineer']
drinks = ['tea', 'milk', 'water', 'root beer', 'coffee']

# Initialize the houses with empty slots
houses = [{'name': None, 'food': None, 'car_model': None, 'phone_model': None, 'occupation': None, 'drink': None} for _ in range(5)]

def is_valid(state):
    # Extract the current state into separate lists for easier access
    names_state = [house['name'] for house in state]
    foods_state = [house['food'] for house in state]
    car_models_state = [house['car_model'] for house in state]
    phone_models_state = [house['phone_model'] for house in state]
    occupations_state = [house['occupation'] for house in state]
    drinks_state = [house['drink'] for house in state]

    # Check constraints
    if drinks_state.index('root beer') != car_models_state.index('honda civic'):
        return False
    if drinks_state.index('milk') + 1 != foods_state.index('grilled cheese'):
        return False
    if names_state.index('Alice') != phone_models_state.index('samsung galaxy s21'):
        return False
    if names_state.index('Alice') != foods_state.index('stir fry'):
        return False
    if drinks_state[4] == 'tea':
        return False
    if car_models_state.index('bmw 3 series') > drinks_state.index('tea'):
        return False
    if occupations_state.index('doctor') != names_state.index('Arnold'):
        return False
    if phone_models_state.index('iphone 13') != drinks_state.index('coffee'):
        return False
    if occupations_state.index('engineer') != car_models_state.index('bmw 3 series'):
        return False
    if foods_state.index('stew') != phone_models_state.index('iphone 13'):
        return False
    if occupations_state.index('doctor') + 1 != phone_models_state.index('oneplus 9'):
        return False
    if car_models_state.index('honda civic') + 1 != foods_state.index('spaghetti'):
        return False
    if phone_models_state.index('google pixel 6') != drinks_state.index('tea'):
        return False
    if occupations_state.index('artist') != names_state.index('Alice'):
        return False
    if abs(names_state.index('Alice') - car_models_state.index('ford f150')) != 1:
        return False
    if car_models_state.index('toyota camry') != names_state.index('Arnold'):
        return False
    if names_state[3] != 'Eric':
        return False
    if phone_models_state.index('oneplus 9') != occupations_state.index('lawyer'):
        return False
    if foods_state.index('grilled cheese') != names_state.index('Peter'):
        return False
    
    return True

def solve(house_index=0):
    if house_index == 5:
        if is_valid(houses):
            return True
        return False
    
    for name in names:
        if name not in [house['name'] for house in houses]:
            houses[house_index]['name'] = name
            for food in foods:
                if food not in [house['food'] for house in houses]:
                    houses[house_index]['food'] = food
                    for car_model in car_models:
                        if car_model not in [house['car_model'] for house in houses]:
                            houses[house_index]['car_model'] = car_model
                            for phone_model in phone_models:
                                if phone_model not in [house['phone_model'] for house in houses]:
                                    houses[house_index]['phone_model'] = phone_model
                                    for occupation in occupations:
                                        if occupation not in [house['occupation'] for house in houses]:
                                            houses[house_index]['occupation'] = occupation
                                            for drink in drinks:
                                                if drink not in [house['drink'] for house in houses]:
                                                    houses[house_index]['drink'] = drink
                                                    if is_valid(houses):
                                                        if solve(house_index + 1):
                                                            return True
                                                    houses[house_index]['drink'] = None
                                            houses[house_index]['occupation'] = None
                                    houses[house_index]['phone_model'] = None
                            houses[house_index]['car_model'] = None
                    houses[house_index]['food'] = None
            houses[house_index]['name'] = None
    return False

solve()

# Prepare the solution in the required JSON format
solution = {
    "solution": {
        "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
        "rows": []
    }
}

for i, house in enumerate(houses, start=1):
    solution["solution"]["rows"].append([
        str(i),
        house['name'],
        house['food'],
        house['car_model'],
        house['phone_model'],
        house['occupation'],
        house['drink']
    ])

print(json.dumps(solution, indent=2))