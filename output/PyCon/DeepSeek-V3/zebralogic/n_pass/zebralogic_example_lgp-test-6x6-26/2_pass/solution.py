import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Peter', 'Carol', 'Eric', 'Alice', 'Bob', 'Arnold']
    phones = ['huawei p50', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'oneplus 9']
    cigars = ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster']
    flowers = ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris']
    colors = ['yellow', 'red', 'green', 'blue', 'white', 'purple']
    sports = ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'phone_{house}', phones)
        problem.addVariable(f'cigar_{house}', cigars)
        problem.addVariable(f'flower_{house}', flowers)
        problem.addVariable(f'color_{house}', colors)
        problem.addVariable(f'sport_{house}', sports)
    
    # All attributes must be different
    for attr in ['name', 'phone', 'cigar', 'flower', 'color', 'sport']:
        problem.addConstraint(AllDifferentConstraint(), [f'{attr}_{house}' for house in houses])
    
    # Clue 1: The person who uses a OnePlus 9 is in the second house.
    problem.addConstraint(lambda phone: phone == 'oneplus 9', ['phone_2'])
    
    # Clue 2: The person who uses a Xiaomi Mi 11 is somewhere to the left of the person who uses a Huawei P50.
    # We need to find which houses have these phones
    for house1 in houses:
        for house2 in houses:
            if house1 < house2:
                problem.addConstraint(
                    lambda p1, p2, h1=house1, h2=house2: not (p1 == 'xiaomi mi 11' and p2 == 'huawei p50') or (h1 < h2),
                    [f'phone_{house1}', f'phone_{house2}']
                )
    
    # Clue 3: Carol is the person who loves a carnations arrangement.
    for house in houses:
        problem.addConstraint(
            lambda name, flower: not (name == 'Carol') or flower == 'carnations',
            [f'name_{house}', f'flower_{house}']
        )
        problem.addConstraint(
            lambda name, flower: not (flower == 'carnations') or name == 'Carol',
            [f'name_{house}', f'flower_{house}']
        )
    
    # Clue 4: The person who loves purple is directly left of the person partial to Pall Mall.
    for i in range(1, 6):
        problem.addConstraint(
            lambda color1, cigar2: not (color1 == 'purple') or cigar2 == 'pall mall',
            [f'color_{i}', f'cigar_{i+1}']
        )
    
    # Clue 5: The person whose favorite color is green is the person who smokes Blue Master.
    for house in houses:
        problem.addConstraint(
            lambda color, cigar: not (color == 'green') or cigar == 'blue master',
            [f'color_{house}', f'cigar_{house}']
        )
        problem.addConstraint(
            lambda color, cigar: not (cigar == 'blue master') or color == 'green',
            [f'color_{house}', f'cigar_{house}']
        )
    
    # Clue 6: The person who loves yellow and the person who loves blue are next to each other.
    for i in range(1, 6):
        problem.addConstraint(
            lambda color1, color2: not (color1 == 'yellow' and color2 == 'blue') and not (color1 == 'blue' and color2 == 'yellow'),
            [f'color_{i}', f'color_{i+1}']
        )
    # Also check the reverse case
    for i in range(1, 6):
        problem.addConstraint(
            lambda color1, color2: (color1 == 'yellow' and color2 == 'blue') or (color1 == 'blue' and color2 == 'yellow'),
            [f'color_{i}', f'color_{i+1}']
        )
    
    # Clue 7: Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
    for house1 in houses:
        for house2 in houses:
            if house1 >= house2:
                problem.addConstraint(
                    lambda name1, phone2, h1=house1, h2=house2: not (name1 == 'Eric' and phone2 == 'samsung galaxy s21') or (h1 > h2),
                    [f'name_{house1}', f'phone_{house2}']
                )
    
    # Clue 8: There are two houses between Carol and the person who loves a bouquet of daffodils.
    for house1 in houses:
        for house2 in houses:
            if abs(house1 - house2) != 3:
                problem.addConstraint(
                    lambda name, flower, h1=house1, h2=house2: not (name == 'Carol' and flower == 'daffodils'),
                    [f'name_{h1}', f'flower_{h2}']
                )
    
    # Clue 9: The Prince smoker is the person who loves basketball.
    for house in houses:
        problem.addConstraint(
            lambda cigar, sport: not (cigar == 'prince') or sport == 'basketball',
            [f'cigar_{house}', f'sport_{house}']
        )
        problem.addConstraint(
            lambda cigar, sport: not (sport == 'basketball') or cigar == 'prince',
            [f'cigar_{house}', f'sport_{house}']
        )
    
    # Clue 10: The Dunhill smoker is the person who loves volleyball.
    for house in houses:
        problem.addConstraint(
            lambda cigar, sport: not (cigar == 'dunhill') or sport == 'volleyball',
            [f'cigar_{house}', f'sport_{house}']
        )
        problem.addConstraint(
            lambda cigar, sport: not (sport == 'volleyball') or cigar == 'dunhill',
            [f'cigar_{house}', f'sport_{house}']
        )
    
    # Clue 11: The person who loves swimming is the person who uses a Google Pixel 6.
    for house in houses:
        problem.addConstraint(
            lambda sport, phone: not (sport == 'swimming') or phone == 'google pixel 6',
            [f'sport_{house}', f'phone_{house}']
        )
        problem.addConstraint(
            lambda sport, phone: not (phone == 'google pixel 6') or sport == 'swimming',
            [f'sport_{house}', f'phone_{house}']
        )
    
    # Clue 12: The person who uses a Huawei P50 is directly left of the person who loves white.
    for i in range(1, 6):
        problem.addConstraint(
            lambda phone, color: not (phone == 'huawei p50') or color == 'white',
            [f'phone_{i}', f'color_{i+1}']
        )
    
    # Clue 13: The person who uses a OnePlus 9 and the person who loves the rose bouquet are next to each other.
    for i in range(1, 6):
        problem.addConstraint(
            lambda phone1, flower2: (phone1 == 'oneplus 9' and flower2 == 'roses') or (flower2 == 'oneplus 9' and phone1 == 'roses'),
            [f'phone_{i}', f'flower_{i+1}']
        )
    
    # Clue 14: The person who loves the bouquet of iris is somewhere to the left of Eric.
    for house1 in houses:
        for house2 in houses:
            if house1 >= house2:
                problem.addConstraint(
                    lambda flower, name, h1=house1, h2=house2: not (flower == 'iris' and name == 'Eric') or (h1 < h2),
                    [f'flower_{h1}', f'name_{h2}']
                )
    
    # Clue 15: The Dunhill smoker is Peter.
    for house in houses:
        problem.addConstraint(
            lambda cigar, name: not (cigar == 'dunhill') or name == 'Peter',
            [f'cigar_{house}', f'name_{house}']
        )
        problem.addConstraint(
            lambda cigar, name: not (name == 'Peter') or cigar == 'dunhill',
            [f'cigar_{house}', f'name_{house}']
        )
    
    # Clue 16: The person who loves blue is Peter.
    for house in houses:
        problem.addConstraint(
            lambda color, name: not (color == 'blue') or name == 'Peter',
            [f'color_{house}', f'name_{house}']
        )
        problem.addConstraint(
            lambda color, name: not (name == 'Peter') or color == 'blue',
            [f'color_{house}', f'name_{house}']
        )
    
    # Clue 17: The person who loves the vase of tulips is Bob.
    for house in houses:
        problem.addConstraint(
            lambda flower, name: not (flower == 'tulips') or name == 'Bob',
            [f'flower_{house}', f'name_{house}']
        )
        problem.addConstraint(
            lambda flower, name: not (name == 'Bob') or flower == 'tulips',
            [f'flower_{house}', f'name_{house}']
        )
    
    # Clue 18: Alice is in the first house.
    problem.addConstraint(lambda name: name == 'Alice', ['name_1'])
    
    # Clue 19: The person who loves baseball is directly left of the person who smokes Blue Master.
    for i in range(1, 6):
        problem.addConstraint(
            lambda sport, cigar: not (sport == 'baseball') or cigar == 'blue master',
            [f'sport_{i}', f'cigar_{i+1}']
        )
    
    # Clue 20: The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes many unique blends.
    for house1 in houses:
        for house2 in houses:
            if house1 <= house2:
                problem.addConstraint(
                    lambda phone, cigar, h1=house1, h2=house2: not (phone == 'google pixel 6' and cigar == 'blends') or (h1 > h2),
                    [f'phone_{h1}', f'cigar_{h2}']
                )
    
    # Clue 21: The person who loves soccer is Carol.
    for house in houses:
        problem.addConstraint(
            lambda sport, name: not (sport == 'soccer') or name == 'Carol',
            [f'sport_{house}', f'name_{house}']
        )
        problem.addConstraint(
            lambda sport, name: not (name == 'Carol') or sport == 'soccer',
            [f'sport_{house}', f'name_{house}']
        )
    
    # Clue 22: The person who loves a carnations arrangement is directly left of the person who smokes many unique blends.
    for i in range(1, 6):
        problem.addConstraint(
            lambda flower, cigar: not (flower == 'carnations') or cigar == 'blends',
            [f'flower_{i}', f'cigar_{i+1}']
        )
    
    # Clue 23: Eric is the person who smokes many unique blends.
    for house in houses:
        problem.addConstraint(
            lambda name, cigar: not (name == 'Eric') or cigar == 'blends',
            [f'name_{house}', f'cigar_{house}']
        )
        problem.addConstraint(
            lambda name, cigar: not (cigar == 'blends') or name == 'Eric',
            [f'name_{house}', f'cigar_{house}']
        )
    
    # Clue 24: The person who loves volleyball is the person who uses an iPhone 13.
    for house in houses:
        problem.addConstraint(
            lambda sport, phone: not (sport == 'volleyball') or phone == 'iphone 13',
            [f'sport_{house}', f'phone_{house}']
        )
        problem.addConstraint(
            lambda sport, phone: not (phone == 'iphone 13') or sport == 'volleyball',
            [f'sport_{house}', f'phone_{house}']
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"]
    rows = []
    
    for house in range(1, 7):
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'phone_{house}'],
            solution[f'cigar_{house}'],
            solution[f'flower_{house}'],
            solution[f'color_{house}'],
            solution[f'sport_{house}']
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))