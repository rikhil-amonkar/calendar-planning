import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
    smoothies = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
    nationalities = ['german', 'swede', 'norwegian', 'dane', 'brit']
    
    # Generate all possible permutations for each category
    name_perms = list(permutations(names))
    smoothie_perms = list(permutations(smoothies))
    nationality_perms = list(permutations(nationalities))
    
    # Try all combinations
    for name_assignment in name_perms:
        for smoothie_assignment in smoothie_perms:
            for nationality_assignment in nationality_perms:
                # Create house assignments (house 1 to 5)
                assignment = []
                for i in range(5):
                    house = {
                        'house': i + 1,
                        'name': name_assignment[i],
                        'smoothie': smoothie_assignment[i],
                        'nationality': nationality_assignment[i]
                    }
                    assignment.append(house)
                
                # Check all constraints
                valid = True
                
                # Clue 1: The Dragonfruit smoothie lover is somewhere to the left of Eric
                dragonfruit_house = None
                eric_house = None
                for house in assignment:
                    if house['smoothie'] == 'dragonfruit':
                        dragonfruit_house = house['house']
                    if house['name'] == 'Eric':
                        eric_house = house['house']
                if dragonfruit_house is None or eric_house is None or dragonfruit_house >= eric_house:
                    valid = False
                    continue
                
                # Clue 2: The Dragonfruit smoothie lover is in the second house
                if dragonfruit_house != 2:
                    valid = False
                    continue
                
                # Clue 3: Peter is not in the first house
                if assignment[0]['name'] == 'Peter':
                    valid = False
                    continue
                
                # Clue 4: The Dane and the British person are next to each other
                dane_house = None
                brit_house = None
                for house in assignment:
                    if house['nationality'] == 'dane':
                        dane_house = house['house']
                    if house['nationality'] == 'brit':
                        brit_house = house['house']
                if dane_house is None or brit_house is None or abs(dane_house - brit_house) != 1:
                    valid = False
                    continue
                
                # Clue 5: The Desert smoothie lover is not in the fifth house
                if assignment[4]['smoothie'] == 'desert':
                    valid = False
                    continue
                
                # Clue 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover
                swede_house = None
                for house in assignment:
                    if house['nationality'] == 'swede':
                        swede_house = house['house']
                if swede_house is None or swede_house >= dragonfruit_house:
                    valid = False
                    continue
                
                # Clue 7: There are two houses between the person who drinks Lime smoothies and the Dane
                lime_house = None
                for house in assignment:
                    if house['smoothie'] == 'lime':
                        lime_house = house['house']
                if lime_house is None or dane_house is None or abs(lime_house - dane_house) != 3:
                    valid = False
                    continue
                
                # Clue 8: Bob is the Dane
                for house in assignment:
                    if house['name'] == 'Bob' and house['nationality'] != 'dane':
                        valid = False
                        break
                    if house['nationality'] == 'dane' and house['name'] != 'Bob':
                        valid = False
                        break
                if not valid:
                    continue
                
                # Clue 9: Alice is the Norwegian
                for house in assignment:
                    if house['name'] == 'Alice' and house['nationality'] != 'norwegian':
                        valid = False
                        break
                    if house['nationality'] == 'norwegian' and house['name'] != 'Alice':
                        valid = False
                        break
                if not valid:
                    continue
                
                # Clue 10: Alice is in the third house
                if assignment[2]['name'] != 'Alice':
                    valid = False
                    continue
                
                # Clue 11: The Watermelon smoothie lover is in the third house
                if assignment[2]['smoothie'] != 'watermelon':
                    valid = False
                    continue
                
                # If all constraints are satisfied, return the solution
                if valid:
                    return assignment
    
    return None

def main():
    solution = solve_puzzle()
    
    if solution:
        # Format the solution as required
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": []
            }
        }
        
        for house in sorted(solution, key=lambda x: x['house']):
            result["solution"]["rows"].append([
                str(house['house']),
                house['name'],
                house['smoothie'],
                house['nationality']
            ])
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()