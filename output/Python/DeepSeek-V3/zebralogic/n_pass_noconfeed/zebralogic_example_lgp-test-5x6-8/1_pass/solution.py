import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Arnold', 'Bob', 'Alice']
    house_styles = ['modern', 'craftsman', 'ranch', 'victorian', 'colonial']
    mothers = ['Penny', 'Kailyn', 'Holly', 'Janelle', 'Aniya']
    phone_models = ['oneplus 9', 'google pixel 6', 'huawei p50', 'iphone 13', 'samsung galaxy s21']
    drinks = ['coffee', 'water', 'root beer', 'tea', 'milk']
    animals = ['fish', 'dog', 'horse', 'bird', 'cat']
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for style_perm in permutations(house_styles):
            for mother_perm in permutations(mothers):
                for phone_perm in permutations(phone_models):
                    for drink_perm in permutations(drinks):
                        for animal_perm in permutations(animals):
                            # Create assignment dictionary
                            assignment = {}
                            for i, house in enumerate(houses):
                                assignment[house] = {
                                    'Name': name_perm[i],
                                    'HouseStyle': style_perm[i],
                                    'Mother': mother_perm[i],
                                    'PhoneModel': phone_perm[i],
                                    'Drink': drink_perm[i],
                                    'Animal': animal_perm[i]
                                }
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: The person who uses a Google Pixel 6 is not in the first house.
                            if assignment[1]['PhoneModel'] == 'google pixel 6':
                                valid = False
                            
                            # Clue 2: The one who only drinks water is Alice.
                            for house in houses:
                                if assignment[house]['Drink'] == 'water' and assignment[house]['Name'] != 'Alice':
                                    valid = False
                                if assignment[house]['Name'] == 'Alice' and assignment[house]['Drink'] != 'water':
                                    valid = False
                            
                            # Clue 3: The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
                            colonial_house = None
                            huawei_house = None
                            for house in houses:
                                if assignment[house]['HouseStyle'] == 'colonial':
                                    colonial_house = house
                                if assignment[house]['PhoneModel'] == 'huawei p50':
                                    huawei_house = house
                            if colonial_house is not None and huawei_house is not None and colonial_house <= huawei_house:
                                valid = False
                            
                            # Clue 4: The person who keeps horses is the person who uses a OnePlus 9.
                            for house in houses:
                                if assignment[house]['Animal'] == 'horse' and assignment[house]['PhoneModel'] != 'oneplus 9':
                                    valid = False
                                if assignment[house]['PhoneModel'] == 'oneplus 9' and assignment[house]['Animal'] != 'horse':
                                    valid = False
                            
                            # Clue 5: The person in a ranch-style home is The person whose mother's name is Kailyn.
                            for house in houses:
                                if assignment[house]['HouseStyle'] == 'ranch' and assignment[house]['Mother'] != 'Kailyn':
                                    valid = False
                                if assignment[house]['Mother'] == 'Kailyn' and assignment[house]['HouseStyle'] != 'ranch':
                                    valid = False
                            
                            # Clue 6: The root beer lover is the cat lover.
                            for house in houses:
                                if assignment[house]['Drink'] == 'root beer' and assignment[house]['Animal'] != 'cat':
                                    valid = False
                                if assignment[house]['Animal'] == 'cat' and assignment[house]['Drink'] != 'root beer':
                                    valid = False
                            
                            # Clue 7: The person living in a colonial-style house is not in the fourth house.
                            if assignment[4]['HouseStyle'] == 'colonial':
                                valid = False
                            
                            # Clue 8: The bird keeper is in the fourth house.
                            if assignment[4]['Animal'] != 'bird':
                                valid = False
                            
                            # Clue 9: The tea drinker is Bob.
                            for house in houses:
                                if assignment[house]['Drink'] == 'tea' and assignment[house]['Name'] != 'Bob':
                                    valid = False
                                if assignment[house]['Name'] == 'Bob' and assignment[house]['Drink'] != 'tea':
                                    valid = False
                            
                            # Clue 10: The tea drinker is somewhere to the right of The person whose mother's name is Kailyn.
                            tea_house = None
                            kailyn_house = None
                            for house in houses:
                                if assignment[house]['Drink'] == 'tea':
                                    tea_house = house
                                if assignment[house]['Mother'] == 'Kailyn':
                                    kailyn_house = house
                            if tea_house is not None and kailyn_house is not None and tea_house <= kailyn_house:
                                valid = False
                            
                            # Clue 11: The root beer lover is somewhere to the left of The person whose mother's name is Kailyn.
                            root_beer_house = None
                            kailyn_house = None
                            for house in houses:
                                if assignment[house]['Drink'] == 'root beer':
                                    root_beer_house = house
                                if assignment[house]['Mother'] == 'Kailyn':
                                    kailyn_house = house
                            if root_beer_house is not None and kailyn_house is not None and root_beer_house >= kailyn_house:
                                valid = False
                            
                            # Clue 12: The person who keeps horses is the person in a modern-style house.
                            for house in houses:
                                if assignment[house]['Animal'] == 'horse' and assignment[house]['HouseStyle'] != 'modern':
                                    valid = False
                                if assignment[house]['HouseStyle'] == 'modern' and assignment[house]['Animal'] != 'horse':
                                    valid = False
                            
                            # Clue 13: The person who uses an iPhone 13 is the person who likes milk.
                            for house in houses:
                                if assignment[house]['PhoneModel'] == 'iphone 13' and assignment[house]['Drink'] != 'milk':
                                    valid = False
                                if assignment[house]['Drink'] == 'milk' and assignment[house]['PhoneModel'] != 'iphone 13':
                                    valid = False
                            
                            # Clue 14: The dog owner is the person who likes milk.
                            for house in houses:
                                if assignment[house]['Animal'] == 'dog' and assignment[house]['Drink'] != 'milk':
                                    valid = False
                                if assignment[house]['Drink'] == 'milk' and assignment[house]['Animal'] != 'dog':
                                    valid = False
                            
                            # Clue 15: The person who uses a Google Pixel 6 is the person in a Craftsman-style house.
                            for house in houses:
                                if assignment[house]['PhoneModel'] == 'google pixel 6' and assignment[house]['HouseStyle'] != 'craftsman':
                                    valid = False
                                if assignment[house]['HouseStyle'] == 'craftsman' and assignment[house]['PhoneModel'] != 'google pixel 6':
                                    valid = False
                            
                            # Clue 16: Eric is not in the second house.
                            if assignment[2]['Name'] == 'Eric':
                                valid = False
                            
                            # Clue 17: The tea drinker is in the fourth house.
                            if assignment[4]['Drink'] != 'tea':
                                valid = False
                            
                            # Clue 18: The person who keeps horses is in the third house.
                            if assignment[3]['Animal'] != 'horse':
                                valid = False
                            
                            # Clue 19: The person in a modern-style house is The person whose mother's name is Penny.
                            for house in houses:
                                if assignment[house]['HouseStyle'] == 'modern' and assignment[house]['Mother'] != 'Penny':
                                    valid = False
                                if assignment[house]['Mother'] == 'Penny' and assignment[house]['HouseStyle'] != 'modern':
                                    valid = False
                            
                            # Clue 20: The root beer lover is Peter.
                            for house in houses:
                                if assignment[house]['Drink'] == 'root beer' and assignment[house]['Name'] != 'Peter':
                                    valid = False
                                if assignment[house]['Name'] == 'Peter' and assignment[house]['Drink'] != 'root beer':
                                    valid = False
                            
                            # Clue 21: The person whose mother's name is Aniya is not in the fourth house.
                            if assignment[4]['Mother'] == 'Aniya':
                                valid = False
                            
                            # Clue 22: The person whose mother's name is Janelle is the one who only drinks water.
                            for house in houses:
                                if assignment[house]['Mother'] == 'Janelle' and assignment[house]['Drink'] != 'water':
                                    valid = False
                                if assignment[house]['Drink'] == 'water' and assignment[house]['Mother'] != 'Janelle':
                                    valid = False
                            
                            if valid:
                                # Found the solution
                                result = {
                                    "solution": {
                                        "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                                        "rows": []
                                    }
                                }
                                
                                for house in houses:
                                    row = [
                                        str(house),
                                        assignment[house]['Name'],
                                        assignment[house]['HouseStyle'],
                                        assignment[house]['Mother'],
                                        assignment[house]['PhoneModel'],
                                        assignment[house]['Drink'],
                                        assignment[house]['Animal']
                                    ]
                                    result["solution"]["rows"].append(row)
                                
                                return result
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()