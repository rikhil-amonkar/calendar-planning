import itertools
import json

# Define the attributes
names = ['Eric', 'Peter', 'Arnold']
drinks = ['milk', 'water', 'tea']
vacations = ['mountain', 'city', 'beach']
housestyles = ['colonial', 'victorian', 'ranch']
animals = ['cat', 'bird', 'horse']
birthdays = ['jan', 'sept', 'april']

# Generate all possible permutations for each attribute
all_permutations = list(itertools.permutations(names)) + \
                   list(itertools.permutations(drinks)) + \
                   list(itertools.permutations(vacations)) + \
                   list(itertools.permutations(housestyles)) + \
                   list(itertools.permutations(animals)) + \
                   list(itertools.permutations(birthdays))

# Function to validate a solution against all clues
def is_valid_solution(solution):
    # Unpack the solution into separate lists for each attribute
    name_order, drink_order, vacation_order, housestyle_order, animal_order, birthday_order = solution
    
    # Apply each clue
    # Clue 1: The person living in a colonial-style house is somewhere to the left of the person who likes milk.
    if housestyle_order.index('colonial') >= drink_order.index('milk'):
        return False
    
    # Clue 2: The person who prefers city breaks is directly left of the person residing in a Victorian house.
    if vacation_order.index('city') + 1 != housestyle_order.index('victorian'):
        return False
    
    # Clue 3: The person whose birthday is in January is directly left of the cat lover.
    if birthday_order.index('jan') + 1 != animal_order.index('cat'):
        return False
    
    # Clue 4: The one who only drinks water is the person who enjoys mountain retreats.
    if drink_order.index('water') != vacation_order.index('mountain'):
        return False
    
    # Clue 5: The person who keeps horses is Peter.
    if animal_order.index('horse') != name_order.index('Peter'):
        return False
    
    # Clue 6: The person residing in a Victorian house is somewhere to the right of the person who loves beach vacations.
    if housestyle_order.index('victorian') <= vacation_order.index('beach'):
        return False
    
    # Clue 7: Peter is the person who prefers city breaks.
    if name_order.index('Peter') != vacation_order.index('city'):
        return False
    
    # Clue 8: The person who enjoys mountain retreats is the person whose birthday is in April.
    if vacation_order.index('mountain') != birthday_order.index('april'):
        return False
    
    # Clue 9: Eric is the one who only drinks water.
    if name_order.index('Eric') != drink_order.index('water'):
        return False
    
    return True

# Iterate over all possible combinations of permutations
for names_perm in itertools.permutations(names):
    for drinks_perm in itertools.permutations(drinks):
        for vacations_perm in itertools.permutations(vacations):
            for housestyles_perm in itertools.permutations(housestyles):
                for animals_perm in itertools.permutations(animals):
                    for birthdays_perm in itertools.permutations(birthdays):
                        solution = [names_perm, drinks_perm, vacations_perm, housestyles_perm, animals_perm, birthdays_perm]
                        if is_valid_solution(solution):
                            # Format the solution as required
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                                    "rows": [
                                        ["1", names_perm[0], drinks_perm[0], vacations_perm[0], housestyles_perm[0], animals_perm[0], birthdays_perm[0]],
                                        ["2", names_perm[1], drinks_perm[1], vacations_perm[1], housestyles_perm[1], animals_perm[1], birthdays_perm[1]],
                                        ["3", names_perm[2], drinks_perm[2], vacations_perm[2], housestyles_perm[2], animals_perm[2], birthdays_perm[2]]
                                    ]
                                }
                            }
                            # Output the solution as JSON
                            print(json.dumps(result, indent=2))
                            break