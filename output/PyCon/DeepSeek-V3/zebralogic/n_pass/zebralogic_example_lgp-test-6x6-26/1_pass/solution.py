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
    def left_of(xiaomi_house, huawei_house):
        return xiaomi_house < huawei_house
    problem.addConstraint(left_of, ['phone_xiaomi', 'phone_huawei'])
    
    # Clue 3: Carol is the person who loves a carnations arrangement.
    problem.addConstraint(lambda name, flower: (name == 'Carol') == (flower == 'carnations'), 
                         ['name_carnations', 'flower_carnations'])
    
    # Clue 4: The person who loves purple is directly left of the person partial to Pall Mall.
    def directly_left(purple_house, pallmall_house):
        return purple_house + 1 == pallmall_house
    problem.addConstraint(directly_left, ['color_purple', 'cigar_pallmall'])
    
    # Clue 5: The person whose favorite color is green is the person who smokes Blue Master.
    problem.addConstraint(lambda color, cigar: (color == 'green') == (cigar == 'blue master'), 
                         ['color_green', 'cigar_blue_master'])
    
    # Clue 6: The person who loves yellow and the person who loves blue are next to each other.
    def adjacent(yellow_house, blue_house):
        return abs(yellow_house - blue_house) == 1
    problem.addConstraint(adjacent, ['color_yellow', 'color_blue'])
    
    # Clue 7: Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
    def right_of(eric_house, samsung_house):
        return eric_house > samsung_house
    problem.addConstraint(right_of, ['name_eric', 'phone_samsung'])
    
    # Clue 8: There are two houses between Carol and the person who loves a bouquet of daffodils.
    def two_houses_between(carol_house, daffodils_house):
        return abs(carol_house - daffodils_house) == 3
    problem.addConstraint(two_houses_between, ['name_carol', 'flower_daffodils'])
    
    # Clue 9: The Prince smoker is the person who loves basketball.
    problem.addConstraint(lambda cigar, sport: (cigar == 'prince') == (sport == 'basketball'), 
                         ['cigar_prince', 'sport_basketball'])
    
    # Clue 10: The Dunhill smoker is the person who loves volleyball.
    problem.addConstraint(lambda cigar, sport: (cigar == 'dunhill') == (sport == 'volleyball'), 
                         ['cigar_dunhill', 'sport_volleyball'])
    
    # Clue 11: The person who loves swimming is the person who uses a Google Pixel 6.
    problem.addConstraint(lambda sport, phone: (sport == 'swimming') == (phone == 'google pixel 6'), 
                         ['sport_swimming', 'phone_google'])
    
    # Clue 12: The person who uses a Huawei P50 is directly left of the person who loves white.
    def directly_left_huawei(huawei_house, white_house):
        return huawei_house + 1 == white_house
    problem.addConstraint(directly_left_huawei, ['phone_huawei', 'color_white'])
    
    # Clue 13: The person who uses a OnePlus 9 and the person who loves the rose bouquet are next to each other.
    def adjacent_oneplus_rose(oneplus_house, rose_house):
        return abs(oneplus_house - rose_house) == 1
    problem.addConstraint(adjacent_oneplus_rose, ['phone_oneplus', 'flower_rose'])
    
    # Clue 14: The person who loves the bouquet of iris is somewhere to the left of Eric.
    def left_of_iris(iris_house, eric_house):
        return iris_house < eric_house
    problem.addConstraint(left_of_iris, ['flower_iris', 'name_eric'])
    
    # Clue 15: The Dunhill smoker is Peter.
    problem.addConstraint(lambda cigar, name: (cigar == 'dunhill') == (name == 'Peter'), 
                         ['cigar_dunhill', 'name_peter'])
    
    # Clue 16: The person who loves blue is Peter.
    problem.addConstraint(lambda color, name: (color == 'blue') == (name == 'Peter'), 
                         ['color_blue', 'name_peter'])
    
    # Clue 17: The person who loves the vase of tulips is Bob.
    problem.addConstraint(lambda flower, name: (flower == 'tulips') == (name == 'Bob'), 
                         ['flower_tulips', 'name_bob'])
    
    # Clue 18: Alice is in the first house.
    problem.addConstraint(lambda name: name == 'Alice', ['name_1'])
    
    # Clue 19: The person who loves baseball is directly left of the person who smokes Blue Master.
    def directly_left_baseball(baseball_house, bluemaster_house):
        return baseball_house + 1 == bluemaster_house
    problem.addConstraint(directly_left_baseball, ['sport_baseball', 'cigar_blue_master'])
    
    # Clue 20: The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes many unique blends.
    def right_of_google(google_house, blends_house):
        return google_house > blends_house
    problem.addConstraint(right_of_google, ['phone_google', 'cigar_blends'])
    
    # Clue 21: The person who loves soccer is Carol.
    problem.addConstraint(lambda sport, name: (sport == 'soccer') == (name == 'Carol'), 
                         ['sport_soccer', 'name_carol'])
    
    # Clue 22: The person who loves a carnations arrangement is directly left of the person who smokes many unique blends.
    def directly_left_carnations(carnations_house, blends_house):
        return carnations_house + 1 == blends_house
    problem.addConstraint(directly_left_carnations, ['flower_carnations', 'cigar_blends'])
    
    # Clue 23: Eric is the person who smokes many unique blends.
    problem.addConstraint(lambda name, cigar: (name == 'Eric') == (cigar == 'blends'), 
                         ['name_eric', 'cigar_blends'])
    
    # Clue 24: The person who loves volleyball is the person who uses an iPhone 13.
    problem.addConstraint(lambda sport, phone: (sport == 'volleyball') == (phone == 'iphone 13'), 
                         ['sport_volleyball', 'phone_iphone'])
    
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