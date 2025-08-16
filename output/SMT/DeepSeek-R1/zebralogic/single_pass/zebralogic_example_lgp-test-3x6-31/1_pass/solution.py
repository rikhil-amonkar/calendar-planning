import z3
import json

def main():
    # Define the categories and their possible values
    categories = {
        'Name': ['Eric', 'Peter', 'Arnold'],
        'Drink': ['milk', 'water', 'tea'],
        'Vacation': ['mountain', 'city', 'beach'],
        'HouseStyle': ['colonial', 'victorian', 'ranch'],
        'Animal': ['cat', 'bird', 'horse'],
        'Birthday': ['jan', 'sept', 'april']
    }
    
    # Create enum sorts and constants for each category
    sorts = {}
    consts = {}
    for cat, values in categories.items():
        sort = z3.EnumSort(cat, values)
        sorts[cat] = sort
        consts[cat] = {val: sort[val] for val in values}
    
    n = 3  # Number of houses
    variables = {}
    for cat in categories:
        variables[cat] = [z3.Const(f'{cat}_{i}', sorts[cat]) for i in range(n)]
    
    s = z3.Solver()
    
    # Add distinct constraints for each attribute category
    for cat in categories:
        s.add(z3.Distinct(variables[cat]))
    
    # Extract variables for easier reference
    name = variables['Name']
    drink = variables['Drink']
    vacation = variables['Vacation']
    house_style = variables['HouseStyle']
    animal = variables['Animal']
    birthday = variables['Birthday']
    
    # Define constants for attribute values
    colonial = consts['HouseStyle']['colonial']
    milk = consts['Drink']['milk']
    city = consts['Vacation']['city']
    victorian = consts['HouseStyle']['victorian']
    jan = consts['Birthday']['jan']
    cat_val = consts['Animal']['cat']
    water = consts['Drink']['water']
    mountain = consts['Vacation']['mountain']
    horse = consts['Animal']['horse']
    peter = consts['Name']['Peter']
    beach = consts['Vacation']['beach']
    april = consts['Birthday']['april']
    eric = consts['Name']['Eric']
    
    # Clue 1: Colonial house is left of milk drinker
    s.add(z3.Or(
        z3.And(house_style[0] == colonial, z3.Or(drink[1] == milk, drink[2] == milk)),
        z3.And(house_style[1] == colonial, drink[2] == milk)
    ))
    
    # Clue 2: City vacation directly left of Victorian house
    s.add(z3.Or(
        z3.And(vacation[0] == city, house_style[1] == victorian),
        z3.And(vacation[1] == city, house_style[2] == victorian)
    ))
    
    # Clue 3: January birthday directly left of cat lover
    s.add(z3.Or(
        z3.And(birthday[0] == jan, animal[1] == cat_val),
        z3.And(birthday[1] == jan, animal[2] == cat_val)
    ))
    
    # Clue 4: Water drinker is mountain retreat lover
    for i in range(n):
        s.add((drink[i] == water) == (vacation[i] == mountain))
    
    # Clue 5: Horse keeper is Peter
    for i in range(n):
        s.add((animal[i] == horse) == (name[i] == peter))
    
    # Clue 6: Beach vacation left of Victorian house
    s.add(z3.Or(
        z3.And(vacation[0] == beach, z3.Or(house_style[1] == victorian, house_style[2] == victorian)),
        z3.And(vacation[1] == beach, house_style[2] == victorian)
    ))
    
    # Clue 7: Peter prefers city vacations
    for i in range(n):
        s.add((name[i] == peter) == (vacation[i] == city))
    
    # Clue 8: Mountain retreat lover has April birthday
    for i in range(n):
        s.add((vacation[i] == mountain) == (birthday[i] == april))
    
    # Clue 9: Eric drinks water
    for i in range(n):
        s.add((name[i] == eric) == (drink[i] == water))
    
    # Solve the constraints
    if s.check() == z3.sat:
        m = s.model()
        rows = []
        for i in range(n):
            house_num = str(i+1)
            name_val = None
            for k, v in consts['Name'].items():
                if m.evaluate(name[i]) == v:
                    name_val = k
                    break
            drink_val = None
            for k, v in consts['Drink'].items():
                if m.evaluate(drink[i]) == v:
                    drink_val = k
                    break
            vacation_val = None
            for k, v in consts['Vacation'].items():
                if m.evaluate(vacation[i]) == v:
                    vacation_val = k
                    break
            house_style_val = None
            for k, v in consts['HouseStyle'].items():
                if m.evaluate(house_style[i]) == v:
                    house_style_val = k
                    break
            animal_val = None
            for k, v in consts['Animal'].items():
                if m.evaluate(animal[i]) == v:
                    animal_val = k
                    break
            birthday_val = None
            for k, v in consts['Birthday'].items():
                if m.evaluate(birthday[i]) == v:
                    birthday_val = k
                    break
            row = [house_num, name_val, drink_val, vacation_val, house_style_val, animal_val, birthday_val]
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print('{"error": "unsatisfiable"}')

if __name__ == "__main__":
    main()