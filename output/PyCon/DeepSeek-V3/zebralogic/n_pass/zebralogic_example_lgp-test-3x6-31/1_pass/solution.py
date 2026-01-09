import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1, 2, 3)
    houses = [1, 2, 3]
    
    # Define domains for each attribute
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['milk', 'water', 'tea']
    vacations = ['mountain', 'city', 'beach']
    house_styles = ['colonial', 'victorian', 'ranch']
    animals = ['cat', 'bird', 'horse']
    birthdays = ['jan', 'sept', 'april']
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'drink_{house}', drinks)
        problem.addVariable(f'vacation_{house}', vacations)
        problem.addVariable(f'house_style_{house}', house_styles)
        problem.addVariable(f'animal_{house}', animals)
        problem.addVariable(f'birthday_{house}', birthdays)
    
    # All attributes must be different across houses
    for attr in ['name', 'drink', 'vacation', 'house_style', 'animal', 'birthday']:
        problem.addConstraint(AllDifferentConstraint(), [f'{attr}_{house}' for house in houses])
    
    # Clue 1: The person living in a colonial-style house is somewhere to the left of the person who likes milk.
    def left_of_colonial_milk(h1_style, h1_drink, h2_style, h2_drink, h3_style, h3_drink):
        colonial_house = None
        milk_house = None
        for i, (style, drink) in enumerate([(h1_style, h1_drink), (h2_style, h2_drink), (h3_style, h3_drink)]):
            if style == 'colonial':
                colonial_house = i + 1
            if drink == 'milk':
                milk_house = i + 1
        return colonial_house is not None and milk_house is not None and colonial_house < milk_house
    
    problem.addConstraint(left_of_colonial_milk, 
                         ['house_style_1', 'drink_1', 'house_style_2', 'drink_2', 'house_style_3', 'drink_3'])
    
    # Clue 2: The person who prefers city breaks is directly left of the person residing in a Victorian house.
    def city_left_of_victorian(h1_vac, h1_style, h2_vac, h2_style, h3_vac, h3_style):
        for i in range(2):
            vacs = [h1_vac, h2_vac, h3_vac]
            styles = [h1_style, h2_style, h3_style]
            if vacs[i] == 'city' and styles[i+1] == 'victorian':
                return True
        return False
    
    problem.addConstraint(city_left_of_victorian, 
                         ['vacation_1', 'house_style_1', 'vacation_2', 'house_style_2', 'vacation_3', 'house_style_3'])
    
    # Clue 3: The person whose birthday is in January is directly left of the cat lover.
    def jan_left_of_cat(h1_bday, h1_animal, h2_bday, h2_animal, h3_bday, h3_animal):
        for i in range(2):
            bdays = [h1_bday, h2_bday, h3_bday]
            animals = [h1_animal, h2_animal, h3_animal]
            if bdays[i] == 'jan' and animals[i+1] == 'cat':
                return True
        return False
    
    problem.addConstraint(jan_left_of_cat, 
                         ['birthday_1', 'animal_1', 'birthday_2', 'animal_2', 'birthday_3', 'animal_3'])
    
    # Clue 4: The one who only drinks water is the person who enjoys mountain retreats.
    def water_is_mountain(drink, vacation):
        return (drink == 'water') == (vacation == 'mountain')
    
    for house in houses:
        problem.addConstraint(water_is_mountain, [f'drink_{house}', f'vacation_{house}'])
    
    # Clue 5: The person who keeps horses is Peter.
    def horse_is_peter(animal, name):
        return (animal == 'horse') == (name == 'Peter')
    
    for house in houses:
        problem.addConstraint(horse_is_peter, [f'animal_{house}', f'name_{house}'])
    
    # Clue 6: The person residing in a Victorian house is somewhere to the right of the person who loves beach vacations.
    def victorian_right_of_beach(h1_style, h1_vac, h2_style, h2_vac, h3_style, h3_vac):
        victorian_house = None
        beach_house = None
        for i, (style, vac) in enumerate([(h1_style, h1_vac), (h2_style, h2_vac), (h3_style, h3_vac)]):
            if style == 'victorian':
                victorian_house = i + 1
            if vac == 'beach':
                beach_house = i + 1
        return victorian_house is not None and beach_house is not None and victorian_house > beach_house
    
    problem.addConstraint(victorian_right_of_beach, 
                         ['house_style_1', 'vacation_1', 'house_style_2', 'vacation_2', 'house_style_3', 'vacation_3'])
    
    # Clue 7: Peter is the person who prefers city breaks.
    def peter_is_city(name, vacation):
        return (name == 'Peter') == (vacation == 'city')
    
    for house in houses:
        problem.addConstraint(peter_is_city, [f'name_{house}', f'vacation_{house}'])
    
    # Clue 8: The person who enjoys mountain retreats is the person whose birthday is in April.
    def mountain_is_april(vacation, birthday):
        return (vacation == 'mountain') == (birthday == 'april')
    
    for house in houses:
        problem.addConstraint(mountain_is_april, [f'vacation_{house}', f'birthday_{house}'])
    
    # Clue 9: Eric is the one who only drinks water.
    def eric_is_water(name, drink):
        return (name == 'Eric') == (drink == 'water')
    
    for house in houses:
        problem.addConstraint(eric_is_water, [f'name_{house}', f'drink_{house}'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the output structure
    header = ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'drink_{house}'],
            solution[f'vacation_{house}'],
            solution[f'house_style_{house}'],
            solution[f'animal_{house}'],
            solution[f'birthday_{house}']
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))