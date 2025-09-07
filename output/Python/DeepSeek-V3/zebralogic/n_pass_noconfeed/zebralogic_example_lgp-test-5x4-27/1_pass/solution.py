import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
    birthdays = ['april', 'feb', 'mar', 'jan', 'sept']
    cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
    drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']
    houses = ['1', '2', '3', '4', '5']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for bday_perm in permutations(birthdays):
            for cigar_perm in permutations(cigars):
                for drink_perm in permutations(drinks):
                    # Create assignment for each house
                    assignment = []
                    for i in range(5):
                        house = {
                            'House': str(i + 1),
                            'Name': name_perm[i],
                            'Birthday': bday_perm[i],
                            'Cigar': cigar_perm[i],
                            'Drink': drink_perm[i]
                        }
                        assignment.append(house)
                    
                    # Check all constraints
                    valid = True
                    
                    # Constraint 1: The root beer lover is Eric
                    root_beer_house = None
                    for house in assignment:
                        if house['Drink'] == 'root beer':
                            root_beer_house = house
                            break
                    if not root_beer_house or root_beer_house['Name'] != 'Eric':
                        valid = False
                        continue
                    
                    # Constraint 2: Pall Mall smoker in third house
                    if assignment[2]['Cigar'] != 'pall mall':
                        valid = False
                        continue
                    
                    # Constraint 3: April birthday is Bob
                    for house in assignment:
                        if house['Birthday'] == 'april' and house['Name'] != 'Bob':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Constraint 4: Dunhill smoker has March birthday
                    for house in assignment:
                        if house['Cigar'] == 'dunhill' and house['Birthday'] != 'mar':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Constraint 5: Peter is right of root beer lover
                    peter_house = None
                    for house in assignment:
                        if house['Name'] == 'Peter':
                            peter_house = house
                            break
                    if not peter_house or int(peter_house['House']) <= int(root_beer_house['House']):
                        valid = False
                        continue
                    
                    # Constraint 6: One house between January birthday and Peter
                    jan_house = None
                    for house in assignment:
                        if house['Birthday'] == 'jan':
                            jan_house = house
                            break
                    if not jan_house or abs(int(jan_house['House']) - int(peter_house['House'])) != 2:
                        valid = False
                        continue
                    
                    # Constraint 7: Blends smoker has February birthday
                    for house in assignment:
                        if house['Cigar'] == 'blends' and house['Birthday'] != 'feb':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Constraint 8: February birthday in second house
                    if assignment[1]['Birthday'] != 'feb':
                        valid = False
                        continue
                    
                    # Constraint 9: Arnold directly left of Peter
                    arnold_house = None
                    for house in assignment:
                        if house['Name'] == 'Arnold':
                            arnold_house = house
                            break
                    if not arnold_house or int(arnold_house['House']) + 1 != int(peter_house['House']):
                        valid = False
                        continue
                    
                    # Constraint 10: Milk not in fifth house
                    if assignment[4]['Drink'] == 'milk':
                        valid = False
                        continue
                    
                    # Constraint 11: Blue Master smoker is coffee drinker
                    for house in assignment:
                        if house['Cigar'] == 'blue master' and house['Drink'] != 'coffee':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Constraint 12: One house between tea and coffee drinker
                    tea_house = None
                    coffee_house = None
                    for house in assignment:
                        if house['Drink'] == 'tea':
                            tea_house = house
                        elif house['Drink'] == 'coffee':
                            coffee_house = house
                    if not tea_house or not coffee_house or abs(int(tea_house['House']) - int(coffee_house['House'])) != 2:
                        valid = False
                        continue
                    
                    # Constraint 13: Eric in third house
                    if assignment[2]['Name'] != 'Eric':
                        valid = False
                        continue
                    
                    if valid:
                        # Format the solution
                        rows = []
                        for house in sorted(assignment, key=lambda x: int(x['House'])):
                            rows.append([
                                house['House'],
                                house['Name'],
                                house['Birthday'],
                                house['Cigar'],
                                house['Drink']
                            ])
                        
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                                "rows": rows
                            }
                        }
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