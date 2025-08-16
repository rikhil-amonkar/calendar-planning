import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    cigars = ['prince', 'dunhill', 'blue master', 'pall mall']
    sports = ['swimming', 'basketball', 'soccer', 'tennis']
    drinks = ['coffee', 'water', 'milk', 'tea']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for cigar_perm in permutations(cigars):
            for sport_perm in permutations(sports):
                for drink_perm in permutations(drinks):
                    # Create a solution candidate
                    solution = []
                    for i in range(4):
                        house = {
                            'House': str(i+1),
                            'Name': name_perm[i],
                            'Cigar': cigar_perm[i],
                            'FavoriteSport': sport_perm[i],
                            'Drink': drink_perm[i]
                        }
                        solution.append(house)
                    
                    # Check all constraints
                    valid = True
                    
                    # 1. Peter is in the fourth house.
                    if solution[3]['Name'] != 'Peter':
                        valid = False
                        continue
                    
                    # 2. The tea drinker is the person who loves basketball.
                    tea_drinker = None
                    basketball_player = None
                    for house in solution:
                        if house['Drink'] == 'tea':
                            tea_drinker = house['Name']
                        if house['FavoriteSport'] == 'basketball':
                            basketball_player = house['Name']
                    if tea_drinker != basketball_player:
                        valid = False
                        continue
                    
                    # 3. Arnold is the person who smokes Blue Master.
                    arnold_house = None
                    for house in solution:
                        if house['Name'] == 'Arnold':
                            arnold_house = house
                    if not arnold_house or arnold_house['Cigar'] != 'blue master':
                        valid = False
                        continue
                    
                    # 4. The person who loves basketball is Eric.
                    if basketball_player != 'Eric':
                        valid = False
                        continue
                    
                    # 5. The person who loves tennis is the person who smokes Blue Master.
                    tennis_player = None
                    blue_master_smoker = None
                    for house in solution:
                        if house['FavoriteSport'] == 'tennis':
                            tennis_player = house['Name']
                        if house['Cigar'] == 'blue master':
                            blue_master_smoker = house['Name']
                    if tennis_player != blue_master_smoker:
                        valid = False
                        continue
                    
                    # 6. There are two houses between the one who only drinks water and Peter.
                    water_drinker_house = None
                    for house in solution:
                        if house['Drink'] == 'water':
                            water_drinker_house = int(house['House'])
                    if water_drinker_house is None or (water_drinker_house + 2) != 4:
                        valid = False
                        continue
                    
                    # 7. The coffee drinker is Arnold.
                    if not arnold_house or arnold_house['Drink'] != 'coffee':
                        valid = False
                        continue
                    
                    # 8. The person who loves basketball is in the third house.
                    if solution[2]['FavoriteSport'] != 'basketball':
                        valid = False
                        continue
                    
                    # 9. The Prince smoker is the person who loves soccer.
                    prince_smoker = None
                    soccer_player = None
                    for house in solution:
                        if house['Cigar'] == 'prince':
                            prince_smoker = house['Name']
                        if house['FavoriteSport'] == 'soccer':
                            soccer_player = house['Name']
                    if prince_smoker != soccer_player:
                        valid = False
                        continue
                    
                    # 10. Peter is the person partial to Pall Mall.
                    peter_house = solution[3]
                    if peter_house['Cigar'] != 'pall mall':
                        valid = False
                        continue
                    
                    if valid:
                        # Prepare the output
                        output = {
                            "solution": {
                                "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                                "rows": []
                            }
                        }
                        for house in solution:
                            output["solution"]["rows"].append([
                                house['House'],
                                house['Name'],
                                house['Cigar'],
                                house['FavoriteSport'],
                                house['Drink']
                            ])
                        return output
    return None

solution = solve_puzzle()
print(json.dumps(solution, indent=2))