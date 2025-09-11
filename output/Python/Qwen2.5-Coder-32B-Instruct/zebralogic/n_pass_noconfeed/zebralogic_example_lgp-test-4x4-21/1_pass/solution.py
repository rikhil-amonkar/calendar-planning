import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = [1, 2, 3, 4]
    names = ['Eric', 'Peter', 'Alice', 'Arnold']
    car_models = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
    birthdays = ['jan', 'april', 'sept', 'feb']
    hobbies = ['painting', 'cooking', 'gardening', 'photography']

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(car_models)) + \
                       list(itertools.permutations(birthdays)) + \
                       list(itertools.permutations(hobbies))

    # Iterate over all possible combinations of permutations
    for names_perm in itertools.permutations(names):
        for cars_perm in itertools.permutations(car_models):
            for birthdays_perm in itertools.permutations(birthdays):
                for hobbies_perm in itertools.permutations(hobbies):
                    # Create a dictionary to map each attribute to its position
                    attributes = {
                        'names': {name: idx + 1 for idx, name in enumerate(names_perm)},
                        'cars': {car: idx + 1 for idx, car in enumerate(cars_perm)},
                        'birthdays': {birthday: idx + 1 for idx, birthday in enumerate(birthdays_perm)},
                        'hobbies': {hobby: idx + 1 for idx, hobby in enumerate(hobbies_perm)}
                    }

                    # Check all the clues
                    if (attributes['birthdays']['jan'] != 2 and
                        attributes['hobbies']['photography'] < attributes['names']['Eric'] and
                        attributes['hobbies']['photography'] < attributes['names']['Peter'] and
                        attributes['cars']['honda civic'] + 1 == attributes['cars']['tesla model 3'] and
                        abs(attributes['cars']['tesla model 3'] - attributes['hobbies']['gardening']) == 2 and
                        attributes['cars']['tesla model 3'] == attributes['names']['Arnold'] and
                        attributes['birthdays']['feb'] == attributes['hobbies']['cooking'] and
                        attributes['cars']['toyota camry'] == attributes['names']['Peter'] and
                        attributes['birthdays']['april'] == attributes['names']['Arnold'] and
                        attributes['hobbies']['photography'] == attributes['names']['Alice'] and
                        attributes['birthdays']['jan'] == attributes['names']['Peter']):
                        
                        # If all clues are satisfied, create the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                                "rows": []
                            }
                        }
                        
                        for house in houses:
                            name = names_perm[house - 1]
                            car_model = cars_perm[house - 1]
                            birthday = birthdays_perm[house - 1]
                            hobby = hobbies_perm[house - 1]
                            solution["solution"]["rows"].append([str(house), name, car_model, birthday, hobby])
                        
                        return json.dumps(solution, indent=2)

# Print the solution as JSON
print(solve_puzzle())