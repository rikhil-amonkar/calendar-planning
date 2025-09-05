import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['milk', 'water', 'tea']
    vacations = ['mountain', 'city', 'beach']
    house_styles = ['colonial', 'victorian', 'ranch']
    animals = ['cat', 'bird', 'horse']
    birthdays = ['jan', 'sept', 'april']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for drink_perm in permutations(drinks):
            for vacation_perm in permutations(vacations):
                for house_style_perm in permutations(house_styles):
                    for animal_perm in permutations(animals):
                        for birthday_perm in permutations(birthdays):
                            # Create assignment for house 1, 2, 3
                            assignment = {
                                1: {
                                    'Name': name_perm[0],
                                    'Drink': drink_perm[0],
                                    'Vacation': vacation_perm[0],
                                    'HouseStyle': house_style_perm[0],
                                    'Animal': animal_perm[0],
                                    'Birthday': birthday_perm[0]
                                },
                                2: {
                                    'Name': name_perm[1],
                                    'Drink': drink_perm[1],
                                    'Vacation': vacation_perm[1],
                                    'HouseStyle': house_style_perm[1],
                                    'Animal': animal_perm[1],
                                    'Birthday': birthday_perm[1]
                                },
                                3: {
                                    'Name': name_perm[2],
                                    'Drink': drink_perm[2],
                                    'Vacation': vacation_perm[2],
                                    'HouseStyle': house_style_perm[2],
                                    'Animal': animal_perm[2],
                                    'Birthday': birthday_perm[2]
                                }
                            }
                            
                            # Check all constraints
                            if check_constraints(assignment):
                                return format_solution(assignment)
    
    return None

def check_constraints(assignment):
    # Clue 1: The person living in a colonial-style house is somewhere to the left of the person who likes milk.
    colonial_house = None
    milk_house = None
    for house in [1, 2, 3]:
        if assignment[house]['HouseStyle'] == 'colonial':
            colonial_house = house
        if assignment[house]['Drink'] == 'milk':
            milk_house = house
    if colonial_house is None or milk_house is None or colonial_house >= milk_house:
        return False
    
    # Clue 2: The person who prefers city breaks is directly left of the person residing in a Victorian house.
    city_house = None
    victorian_house = None
    for house in [1, 2, 3]:
        if assignment[house]['Vacation'] == 'city':
            city_house = house
        if assignment[house]['HouseStyle'] == 'victorian':
            victorian_house = house
    if city_house is None or victorian_house is None or victorian_house - city_house != 1:
        return False
    
    # Clue 3: The person whose birthday is in January is directly left of the cat lover.
    jan_house = None
    cat_house = None
    for house in [1, 2, 3]:
        if assignment[house]['Birthday'] == 'jan':
            jan_house = house
        if assignment[house]['Animal'] == 'cat':
            cat_house = house
    if jan_house is None or cat_house is None or cat_house - jan_house != 1:
        return False
    
    # Clue 4: The one who only drinks water is the person who enjoys mountain retreats.
    for house in [1, 2, 3]:
        if assignment[house]['Drink'] == 'water' and assignment[house]['Vacation'] != 'mountain':
            return False
        if assignment[house]['Vacation'] == 'mountain' and assignment[house]['Drink'] != 'water':
            return False
    
    # Clue 5: The person who keeps horses is Peter.
    for house in [1, 2, 3]:
        if assignment[house]['Animal'] == 'horse' and assignment[house]['Name'] != 'Peter':
            return False
        if assignment[house]['Name'] == 'Peter' and assignment[house]['Animal'] != 'horse':
            return False
    
    # Clue 6: The person residing in a Victorian house is somewhere to the right of the person who loves beach vacations.
    beach_house = None
    victorian_house = None
    for house in [1, 2, 3]:
        if assignment[house]['Vacation'] == 'beach':
            beach_house = house
        if assignment[house]['HouseStyle'] == 'victorian':
            victorian_house = house
    if beach_house is None or victorian_house is None or victorian_house <= beach_house:
        return False
    
    # Clue 7: Peter is the person who prefers city breaks.
    for house in [1, 2, 3]:
        if assignment[house]['Name'] == 'Peter' and assignment[house]['Vacation'] != 'city':
            return False
        if assignment[house]['Vacation'] == 'city' and assignment[house]['Name'] != 'Peter':
            return False
    
    # Clue 8: The person who enjoys mountain retreats is the person whose birthday is in April.
    for house in [1, 2, 3]:
        if assignment[house]['Vacation'] == 'mountain' and assignment[house]['Birthday'] != 'april':
            return False
        if assignment[house]['Birthday'] == 'april' and assignment[house]['Vacation'] != 'mountain':
            return False
    
    # Clue 9: Eric is the one who only drinks water.
    for house in [1, 2, 3]:
        if assignment[house]['Name'] == 'Eric' and assignment[house]['Drink'] != 'water':
            return False
        if assignment[house]['Drink'] == 'water' and assignment[house]['Name'] != 'Eric':
            return False
    
    return True

def format_solution(assignment):
    header = ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"]
    rows = []
    
    for house in [1, 2, 3]:
        row = [
            str(house),
            assignment[house]['Name'],
            assignment[house]['Drink'],
            assignment[house]['Vacation'],
            assignment[house]['HouseStyle'],
            assignment[house]['Animal'],
            assignment[house]['Birthday']
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))