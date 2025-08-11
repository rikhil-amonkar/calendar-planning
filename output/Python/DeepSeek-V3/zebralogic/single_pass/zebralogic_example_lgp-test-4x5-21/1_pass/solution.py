import itertools
import json

def solve_puzzle():
    # Define all possible options for each category
    houses = ['1', '2', '3', '4']
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    sports = ['soccer', 'tennis', 'basketball', 'swimming']
    cars = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
    flowers = ['daffodils', 'roses', 'lilies', 'carnations']
    
    # Generate all possible permutations for each category
    for name_perm in itertools.permutations(names):
        for smoothie_perm in itertools.permutations(smoothies):
            for sport_perm in itertools.permutations(sports):
                for car_perm in itertools.permutations(cars):
                    for flower_perm in itertools.permutations(flowers):
                        # Assign each permutation to houses 1-4
                        assignment = []
                        for i in range(4):
                            assignment.append({
                                'House': houses[i],
                                'Name': name_perm[i],
                                'Smoothie': smoothie_perm[i],
                                'Sport': sport_perm[i],
                                'Car': car_perm[i],
                                'Flower': flower_perm[i]
                            })
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 4: The person who loves tennis is in the first house.
                        if assignment[0]['Sport'] != 'tennis':
                            valid = False
                            continue
                        
                        # Clue 8: Eric is the person who loves the rose bouquet.
                        eric_house = None
                        for house in assignment:
                            if house['Name'] == 'Eric':
                                eric_house = house
                                break
                        if not eric_house or eric_house['Flower'] != 'roses':
                            valid = False
                            continue
                        
                        # Clue 1: The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
                        tesla_house = None
                        for house in assignment:
                            if house['Car'] == 'tesla model 3':
                                tesla_house = house
                                break
                        if not tesla_house or tesla_house['Flower'] != 'roses':
                            valid = False
                            continue
                        
                        # Clue 2: Peter is the Dragonfruit smoothie lover.
                        peter_house = None
                        for house in assignment:
                            if house['Name'] == 'Peter':
                                peter_house = house
                                break
                        if not peter_house or peter_house['Smoothie'] != 'dragonfruit':
                            valid = False
                            continue
                        
                        # Clue 3: The Desert smoothie lover is the person who owns a Toyota Camry.
                        desert_house = None
                        for house in assignment:
                            if house['Smoothie'] == 'desert':
                                desert_house = house
                                break
                        if not desert_house or desert_house['Car'] != 'toyota camry':
                            valid = False
                            continue
                        
                        # Clue 5: The person who owns a Toyota Camry and the person who loves basketball are next to each other.
                        basketball_house = None
                        for house in assignment:
                            if house['Sport'] == 'basketball':
                                basketball_house = house
                                break
                        if not basketball_house:
                            valid = False
                            continue
                        toyota_index = houses.index(desert_house['House'])
                        basketball_index = houses.index(basketball_house['House'])
                        if abs(toyota_index - basketball_index) != 1:
                            valid = False
                            continue
                        
                        # Clue 6: Arnold is the person who loves basketball.
                        if basketball_house['Name'] != 'Arnold':
                            valid = False
                            continue
                        
                        # Clue 7: The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
                        honda_house = None
                        for house in assignment:
                            if house['Car'] == 'honda civic':
                                honda_house = house
                                break
                        if not honda_house or honda_house['Flower'] != 'daffodils':
                            valid = False
                            continue
                        
                        # Clue 9: The Watermelon smoothie lover is not in the first house.
                        if assignment[0]['Smoothie'] == 'watermelon':
                            valid = False
                            continue
                        
                        # Clue 10: The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
                        honda_index = houses.index(honda_house['House'])
                        desert_index = houses.index(desert_house['House'])
                        if honda_index <= desert_index:
                            valid = False
                            continue
                        
                        # Clue 11: The person who loves basketball is the person who loves the bouquet of lilies.
                        if basketball_house['Flower'] != 'lilies':
                            valid = False
                            continue
                        
                        # Clue 12: The person who loves tennis and the person who loves soccer are next to each other.
                        tennis_index = None
                        soccer_index = None
                        for i, house in enumerate(assignment):
                            if house['Sport'] == 'tennis':
                                tennis_index = i
                            if house['Sport'] == 'soccer':
                                soccer_index = i
                        if tennis_index is None or soccer_index is None or abs(tennis_index - soccer_index) != 1:
                            valid = False
                            continue
                        
                        if valid:
                            # Prepare the solution in the required format
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "Sport", "Car", "Flower"],
                                    "rows": []
                                }
                            }
                            for house in assignment:
                                solution["solution"]["rows"].append([
                                    house['House'],
                                    house['Name'],
                                    house['Smoothie'],
                                    house['Sport'],
                                    house['Car'],
                                    house['Flower']
                                ])
                            return solution
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))