import constraint
import json

def solve_puzzle():
    problem = constraint.Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
    phones = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
    nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
    colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']
    
    # Add variables for each attribute
    problem.addVariables(['name'], names)
    problem.addVariables(['phone'], phones)
    problem.addVariables(['nationality'], nationalities)
    problem.addVariables(['color'], colors)
    problem.addVariables(['house'], houses)
    
    # All attributes must be different
    problem.addConstraint(constraint.AllDifferentConstraint(), ['name'])
    problem.addConstraint(constraint.AllDifferentConstraint(), ['phone'])
    problem.addConstraint(constraint.AllDifferentConstraint(), ['nationality'])
    problem.addConstraint(constraint.AllDifferentConstraint(), ['color'])
    problem.addConstraint(constraint.AllDifferentConstraint(), ['house'])
    
    # Clue 1: Carol is not in the third house.
    problem.addConstraint(lambda name, house: not (name == 'Carol' and house == 3), ['name', 'house'])
    
    # Clue 2: There is one house between the Dane and the British person.
    problem.addConstraint(lambda nat1, house1, nat2, house2: 
                         ((nat1 == 'dane' and nat2 == 'brit') or (nat1 == 'brit' and nat2 == 'dane')) 
                         and abs(house1 - house2) == 2, 
                         ['nationality', 'house', 'nationality', 'house'])
    
    # Clue 3: Carol is the person whose favorite color is green.
    problem.addConstraint(lambda name, color: name == 'Carol' if color == 'green' else True, ['name', 'color'])
    problem.addConstraint(lambda name, color: color == 'green' if name == 'Carol' else True, ['name', 'color'])
    
    # Clue 4: Arnold is directly left of Alice.
    problem.addConstraint(lambda name1, house1, name2, house2: 
                         not ((name1 == 'Arnold' and name2 == 'Alice') and house1 != house2 - 1), 
                         ['name', 'house', 'name', 'house'])
    
    # Clue 5: Alice is the German.
    problem.addConstraint(lambda name, nationality: name == 'Alice' if nationality == 'german' else True, 
                         ['name', 'nationality'])
    problem.addConstraint(lambda name, nationality: nationality == 'german' if name == 'Alice' else True, 
                         ['name', 'nationality'])
    
    # Clue 6: The person who uses a OnePlus 9 is the person who loves purple.
    problem.addConstraint(lambda phone, color: phone == 'oneplus 9' if color == 'purple' else True, 
                         ['phone', 'color'])
    problem.addConstraint(lambda phone, color: color == 'purple' if phone == 'oneplus 9' else True, 
                         ['phone', 'color'])
    
    # Clue 7: The person who uses a Huawei P50 is not in the third house.
    problem.addConstraint(lambda phone, house: not (phone == 'huawei p50' and house == 3), 
                         ['phone', 'house'])
    
    # Clue 8: The person who uses a Samsung Galaxy S21 is in the fifth house.
    problem.addConstraint(lambda phone, house: phone == 'samsung galaxy s21' if house == 5 else True, 
                         ['phone', 'house'])
    problem.addConstraint(lambda phone, house: house == 5 if phone == 'samsung galaxy s21' else True, 
                         ['phone', 'house'])
    
    # Clue 9: The person who loves white is somewhere to the right of the person whose favorite color is red.
    problem.addConstraint(lambda color1, house1, color2, house2: 
                         not ((color1 == 'white' and color2 == 'red') and house1 <= house2), 
                         ['color', 'house', 'color', 'house'])
    
    # Clue 10: The person who uses a Samsung Galaxy S21 is Bob.
    problem.addConstraint(lambda phone, name: phone == 'samsung galaxy s21' if name == 'Bob' else True, 
                         ['phone', 'name'])
    problem.addConstraint(lambda phone, name: name == 'Bob' if phone == 'samsung galaxy s21' else True, 
                         ['phone', 'name'])
    
    # Clue 11: The Dane is the person who loves yellow.
    problem.addConstraint(lambda nationality, color: nationality == 'dane' if color == 'yellow' else True, 
                         ['nationality', 'color'])
    problem.addConstraint(lambda nationality, color: color == 'yellow' if nationality == 'dane' else True, 
                         ['nationality', 'color'])
    
    # Clue 12: The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
    problem.addConstraint(lambda phone, house1, name, house2: 
                         not (phone == 'samsung galaxy s21' and name == 'Peter' and house1 >= house2), 
                         ['phone', 'house', 'name', 'house'])
    
    # Clue 13: The person who loves blue is Peter.
    problem.addConstraint(lambda color, name: color == 'blue' if name == 'Peter' else True, 
                         ['color', 'name'])
    problem.addConstraint(lambda color, name: name == 'Peter' if color == 'blue' else True, 
                         ['color', 'name'])
    
    # Clue 14: Peter is the British person.
    problem.addConstraint(lambda name, nationality: name == 'Peter' if nationality == 'brit' else True, 
                         ['name', 'nationality'])
    problem.addConstraint(lambda name, nationality: nationality == 'brit' if name == 'Peter' else True, 
                         ['name', 'nationality'])
    
    # Clue 15: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    problem.addConstraint(lambda phone1, house1, phone2, house2: 
                         not ((phone1 == 'samsung galaxy s21' and phone2 == 'iphone 13') and house1 != house2 - 1), 
                         ['phone', 'house', 'phone', 'house'])
    
    # Clue 16: The Norwegian is the person who loves purple.
    problem.addConstraint(lambda nationality, color: nationality == 'norwegian' if color == 'purple' else True, 
                         ['nationality', 'color'])
    problem.addConstraint(lambda nationality, color: color == 'purple' if nationality == 'norwegian' else True, 
                         ['nationality', 'color'])
    
    # Clue 17: The person who uses a Xiaomi Mi 11 is the Chinese.
    problem.addConstraint(lambda phone, nationality: phone == 'xiaomi mi 11' if nationality == 'chinese' else True, 
                         ['phone', 'nationality'])
    problem.addConstraint(lambda phone, nationality: nationality == 'chinese' if phone == 'xiaomi mi 11' else True, 
                         ['phone', 'nationality'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "PhoneModel", "Nationality", "Color"], "rows": []}}
    
    # Convert solutions to house-based format
    house_data = {}
    for sol in solutions:
        house_num = sol['house']
        house_data[house_num] = {
            'name': sol['name'],
            'phone': sol['phone'],
            'nationality': sol['nationality'],
            'color': sol['color']
        }
    
    # Create rows in house order
    rows = []
    for house in sorted(house_data.keys()):
        data = house_data[house]
        rows.append([str(house), data['name'], data['phone'], data['nationality'], data['color']])
    
    return {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))