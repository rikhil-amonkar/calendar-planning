import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4']
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    cigars = ['prince', 'dunhill', 'blue master', 'pall mall']
    sports = ['swimming', 'basketball', 'soccer', 'tennis']
    drinks = ['coffee', 'water', 'milk', 'tea']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for cigar_perm in permutations(cigars):
            for sport_perm in permutations(sports):
                for drink_perm in permutations(drinks):
                    # Create a list of houses with their attributes
                    solution = []
                    for i in range(4):
                        house = {
                            'House': str(i+1),
                            'Name': name_perm[i],
                            'cigar': cigar_perm[i],
                            'sport': sport_perm[i],
                            'drink': drink_perm[i]
                        }
                        solution.append(house)
                    
                    # Check all constraints
                    valid = True
                    
                    # Constraint 1: Peter is in the fourth house
                    if solution[3]['Name'] != 'Peter':
                        valid = False
                        continue
                    
                    # Constraint 2: The tea drinker is the person who loves basketball
                    tea_drinker = None
                    basketball_lover = None
                    for house in solution:
                        if house['drink'] == 'tea':
                            tea_drinker = house['Name']
                        if house['sport'] == 'basketball':
                            basketball_lover = house['Name']
                    if tea_drinker != basketball_lover:
                        valid = False
                        continue
                    
                    # Constraint 3: Arnold is the person who smokes Blue Master
                    arnold_house = None
                    for house in solution:
                        if house['Name'] == 'Arnold':
                            arnold_house = house
                    if arnold_house is None or arnold_house['cigar'] != 'blue master':
                        valid = False
                        continue
                    
                    # Constraint 4: The person who loves basketball is Eric
                    if basketball_lover != 'Eric':
                        valid = False
                        continue
                    
                    # Constraint 5: The person who loves tennis is the person who smokes Blue Master
                    tennis_lover = None
                    blue_master_smoker = None
                    for house in solution:
                        if house['sport'] == 'tennis':
                            tennis_lover = house['Name']
                        if house['cigar'] == 'blue master':
                            blue_master_smoker = house['Name']
                    if tennis_lover != blue_master_smoker:
                        valid = False
                        continue
                    
                    # Constraint 6: There are two houses between the one who only drinks water and Peter
                    water_drinker_house = None
                    for house in solution:
                        if house['drink'] == 'water':
                            water_drinker_house = int(house['House'])
                    if water_drinker_house is None or (water_drinker_house + 2) != 4:
                        valid = False
                        continue
                    
                    # Constraint 7: The coffee drinker is Arnold
                    if arnold_house is None or arnold_house['drink'] != 'coffee':
                        valid = False
                        continue
                    
                    # Constraint 8: The person who loves basketball is in the third house
                    if solution[2]['sport'] != 'basketball':
                        valid = False
                        continue
                    
                    # Constraint 9: The Prince smoker is the person who loves soccer
                    prince_smoker = None
                    soccer_lover = None
                    for house in solution:
                        if house['cigar'] == 'prince':
                            prince_smoker = house['Name']
                        if house['sport'] == 'soccer':
                            soccer_lover = house['Name']
                    if prince_smoker != soccer_lover:
                        valid = False
                        continue
                    
                    # Constraint 10: Peter is the person partial to Pall Mall
                    if solution[3]['cigar'] != 'pall mall':
                        valid = False
                        continue
                    
                    if valid:
                        # Prepare the output
                        output = {
                            "solution": {
                                "header": ["House", "Name", "cigar", "sport", "drink"],
                                "rows": []
                            }
                        }
                        for house in solution:
                            row = [
                                house['House'],
                                house['Name'],
                                house['cigar'],
                                house['sport'],
                                house['drink']
                            ]
                            output["solution"]["rows"].append(row)
                        return output
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))