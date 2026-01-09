import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Peter', 'Bob', 'Carol', 'Eric', 'Alice', 'Arnold']
    pets = ['bird', 'dog', 'cat', 'rabbit', 'fish', 'hamster']
    house_styles = ['victorian', 'ranch', 'modern', 'mediterranean', 'colonial', 'craftsman']
    birthdays = ['mar', 'sept', 'may', 'feb', 'jan', 'april']
    
    # Add variables for each attribute
    problem.addVariables(['name'] + names, houses)
    problem.addVariables(['pet'] + pets, houses)
    problem.addVariables(['style'] + house_styles, houses)
    problem.addVariables(['birthday'] + birthdays, houses)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), ['name_' + n for n in names])
    problem.addConstraint(AllDifferentConstraint(), ['pet_' + p for p in pets])
    problem.addConstraint(AllDifferentConstraint(), ['style_' + s for s in house_styles])
    problem.addConstraint(AllDifferentConstraint(), ['birthday_' + b for b in birthdays])
    
    # Link attribute variables to position variables
    for name in names:
        problem.addConstraint(lambda name_h, h: name_h == h, 
                            (f'name_{name}', f'name'))
    for pet in pets:
        problem.addConstraint(lambda pet_h, h: pet_h == h, 
                            (f'pet_{pet}', f'pet'))
    for style in house_styles:
        problem.addConstraint(lambda style_h, h: style_h == h, 
                            (f'style_{style}', f'style'))
    for birthday in birthdays:
        problem.addConstraint(lambda bday_h, h: bday_h == h, 
                            (f'birthday_{birthday}', f'birthday'))
    
    # Clue 1: Hamster is right of March birthday
    problem.addConstraint(lambda h_hamster, h_mar: h_hamster > h_mar, 
                         ('pet_hamster', 'birthday_mar'))
    
    # Clue 2: January left of September
    problem.addConstraint(lambda h_jan, h_sept: h_jan < h_sept, 
                         ('birthday_jan', 'birthday_sept'))
    
    # Clue 3: May birthday in second house
    problem.addConstraint(lambda h: h == 2, ('birthday_may',))
    
    # Clue 4: Colonial style in second house
    problem.addConstraint(lambda h: h == 2, ('style_colonial',))
    
    # Clue 5: Carol in third house
    problem.addConstraint(lambda h: h == 3, ('name_Carol',))
    
    # Clue 6: Mediterranean not in sixth house
    problem.addConstraint(lambda h: h != 6, ('style_mediterranean',))
    
    # Clue 7: Fish right of Bob
    problem.addConstraint(lambda h_fish, h_bob: h_fish > h_bob, 
                         ('pet_fish', 'name_Bob'))
    
    # Clue 8: Eric in sixth house
    problem.addConstraint(lambda h: h == 6, ('name_Eric',))
    
    # Clue 9: One house between cat and Victorian
    problem.addConstraint(lambda h_cat, h_vic: abs(h_cat - h_vic) == 2, 
                         ('pet_cat', 'style_victorian'))
    
    # Clue 10: Two houses between Victorian and hamster
    problem.addConstraint(lambda h_vic, h_hamster: abs(h_vic - h_hamster) == 3, 
                         ('style_victorian', 'pet_hamster'))
    
    # Clue 11: Craftsman is Arnold
    problem.addConstraint(lambda h_craft, h_arnold: h_craft == h_arnold, 
                         ('style_craftsman', 'name_Arnold'))
    
    # Clue 12: Colonial left of modern
    problem.addConstraint(lambda h_col, h_mod: h_col < h_mod, 
                         ('style_colonial', 'style_modern'))
    
    # Clue 13: Fish not in second house
    problem.addConstraint(lambda h: h != 2, ('pet_fish',))
    
    # Clue 14: Peter is colonial
    problem.addConstraint(lambda h_peter, h_col: h_peter == h_col, 
                         ('name_Peter', 'style_colonial'))
    
    # Clue 15: January directly left of April
    problem.addConstraint(lambda h_jan, h_april: h_jan + 1 == h_april, 
                         ('birthday_jan', 'birthday_april'))
    
    # Clue 16: One house between bird and modern
    problem.addConstraint(lambda h_bird, h_mod: abs(h_bird - h_mod) == 2, 
                         ('pet_bird', 'style_modern'))
    
    # Clue 17: Carol is March birthday
    problem.addConstraint(lambda h_carol, h_mar: h_carol == h_mar, 
                         ('name_Carol', 'birthday_mar'))
    
    # Clue 18: Craftsman in fourth house
    problem.addConstraint(lambda h: h == 4, ('style_craftsman',))
    
    # Clue 19: Dog in fourth house
    problem.addConstraint(lambda h: h == 4, ('pet_dog',))
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    result = {
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": []
        }
    }
    
    # Create mapping from house number to attributes
    house_data = {}
    for house in houses:
        house_data[house] = {
            "name": None,
            "pet": None,
            "style": None,
            "birthday": None
        }
    
    # Fill in the data
    for attr, house_num in solution.items():
        if attr.startswith('name_') and not attr == 'name':
            name = attr[5:]
            house_data[house_num]["name"] = name
        elif attr.startswith('pet_') and not attr == 'pet':
            pet = attr[4:]
            house_data[house_num]["pet"] = pet
        elif attr.startswith('style_') and not attr == 'style':
            style = attr[6:]
            house_data[house_num]["style"] = style
        elif attr.startswith('birthday_') and not attr == 'birthday':
            birthday = attr[9:]
            house_data[house_num]["birthday"] = birthday
    
    # Create rows in house order
    for house_num in sorted(house_data.keys()):
        data = house_data[house_num]
        row = [
            str(house_num),
            data["name"],
            data["pet"],
            data["style"],
            data["birthday"]
        ]
        result["solution"]["rows"].append(row)
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))