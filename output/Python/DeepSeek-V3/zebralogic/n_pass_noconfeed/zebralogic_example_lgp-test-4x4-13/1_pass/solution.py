import itertools
import json

def main():
    # Define the domains
    houses = [1, 2, 3, 4]
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    cigars = ['prince', 'dunhill', 'blue master', 'pall mall']
    sports = ['swimming', 'basketball', 'soccer', 'tennis']
    drinks = ['coffee', 'water', 'milk', 'tea']
    
    # Generate all possible permutations for each attribute
    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            for sport_perm in itertools.permutations(sports):
                for drink_perm in itertools.permutations(drinks):
                    # Create assignment dictionaries
                    assignment = {}
                    for i, house in enumerate(houses):
                        assignment[house] = {
                            'name': name_perm[i],
                            'cigar': cigar_perm[i],
                            'sport': sport_perm[i],
                            'drink': drink_perm[i]
                        }
                    
                    # Check all constraints
                    # Constraint 1: Peter is in the fourth house.
                    if assignment[4]['name'] != 'Peter':
                        continue
                    
                    # Constraint 2: The tea drinker is the person who loves basketball.
                    tea_drinker = None
                    basketball_lover = None
                    for house in houses:
                        if assignment[house]['drink'] == 'tea':
                            tea_drinker = house
                        if assignment[house]['sport'] == 'basketball':
                            basketball_lover = house
                    if tea_drinker != basketball_lover:
                        continue
                    
                    # Constraint 3: Arnold is the person who smokes Blue Master.
                    arnold_house = None
                    blue_master_smoker = None
                    for house in houses:
                        if assignment[house]['name'] == 'Arnold':
                            arnold_house = house
                        if assignment[house]['cigar'] == 'blue master':
                            blue_master_smoker = house
                    if arnold_house != blue_master_smoker:
                        continue
                    
                    # Constraint 4: The person who loves basketball is Eric.
                    basketball_house = None
                    for house in houses:
                        if assignment[house]['sport'] == 'basketball':
                            basketball_house = house
                    if assignment[basketball_house]['name'] != 'Eric':
                        continue
                    
                    # Constraint 5: The person who loves tennis is the person who smokes Blue Master.
                    tennis_lover = None
                    for house in houses:
                        if assignment[house]['sport'] == 'tennis':
                            tennis_lover = house
                    if tennis_lover != blue_master_smoker:
                        continue
                    
                    # Constraint 6: There are two houses between the one who only drinks water and Peter.
                    water_drinker = None
                    for house in houses:
                        if assignment[house]['drink'] == 'water':
                            water_drinker = house
                    if abs(water_drinker - 4) != 2:  # Peter is in house 4
                        continue
                    
                    # Constraint 7: The coffee drinker is Arnold.
                    coffee_drinker = None
                    for house in houses:
                        if assignment[house]['drink'] == 'coffee':
                            coffee_drinker = house
                    if coffee_drinker != arnold_house:
                        continue
                    
                    # Constraint 8: The person who loves basketball is in the third house.
                    if basketball_house != 3:
                        continue
                    
                    # Constraint 9: The Prince smoker is the person who loves soccer.
                    prince_smoker = None
                    soccer_lover = None
                    for house in houses:
                        if assignment[house]['cigar'] == 'prince':
                            prince_smoker = house
                        if assignment[house]['sport'] == 'soccer':
                            soccer_lover = house
                    if prince_smoker != soccer_lover:
                        continue
                    
                    # Constraint 10: Peter is the person partial to Pall Mall.
                    if assignment[4]['cigar'] != 'pall mall':
                        continue
                    
                    # If we reach here, all constraints are satisfied
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        row = [
                            str(house),
                            assignment[house]['name'],
                            assignment[house]['cigar'],
                            assignment[house]['sport'],
                            assignment[house]['drink']
                        ]
                        solution["solution"]["rows"].append(row)
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    print('{"solution": {"header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"], "rows": []}}')

if __name__ == "__main__":
    main()