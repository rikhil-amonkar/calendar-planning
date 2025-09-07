import json
from itertools import permutations

def main():
    # Define all possible values
    names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
    flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
    animals = ['dog', 'horse', 'cat', 'bird', 'fish']
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations
    for name_perm in permutations(names):
        for flower_perm in permutations(flowers):
            for animal_perm in permutations(animals):
                # Create assignment for each house
                assignment = []
                for i in range(5):
                    assignment.append({
                        'house': i+1,
                        'name': name_perm[i],
                        'flower': flower_perm[i],
                        'animal': animal_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Clue 1: Alice is in the second house
                if assignment[1]['name'] != 'Alice':
                    valid = False
                    continue
                
                # Clue 2: The person who loves the bouquet of lilies is the bird keeper
                lilies_house = None
                bird_house = None
                for house in assignment:
                    if house['flower'] == 'lilies':
                        lilies_house = house
                    if house['animal'] == 'bird':
                        bird_house = house
                if lilies_house != bird_house:
                    valid = False
                    continue
                
                # Clue 3: Peter is somewhere to the right of the person who loves the vase of tulips
                peter_house = None
                tulips_house = None
                for house in assignment:
                    if house['name'] == 'Peter':
                        peter_house = house
                    if house['flower'] == 'tulips':
                        tulips_house = house
                if not peter_house or not tulips_house or peter_house['house'] <= tulips_house['house']:
                    valid = False
                    continue
                
                # Clue 4: The fish enthusiast is the person who loves a bouquet of daffodils
                fish_house = None
                daffodils_house = None
                for house in assignment:
                    if house['animal'] == 'fish':
                        fish_house = house
                    if house['flower'] == 'daffodils':
                        daffodils_house = house
                if fish_house != daffodils_house:
                    valid = False
                    continue
                
                # Clue 5: The person who keeps horses is Eric
                horse_house = None
                eric_house = None
                for house in assignment:
                    if house['animal'] == 'horse':
                        horse_house = house
                    if house['name'] == 'Eric':
                        eric_house = house
                if horse_house != eric_house:
                    valid = False
                    continue
                
                # Clue 6: There are two houses between the dog owner and Bob
                dog_house = None
                bob_house = None
                for house in assignment:
                    if house['animal'] == 'dog':
                        dog_house = house
                    if house['name'] == 'Bob':
                        bob_house = house
                if not dog_house or not bob_house or abs(dog_house['house'] - bob_house['house']) != 3:
                    valid = False
                    continue
                
                # Clue 7: The fish enthusiast is directly left of Bob
                if not fish_house or not bob_house or fish_house['house'] != bob_house['house'] - 1:
                    valid = False
                    continue
                
                # Clue 8: Alice is directly left of the person who keeps horses
                if assignment[1]['name'] != 'Alice' or horse_house['house'] != 3:
                    valid = False
                    continue
                
                # Clue 9: The person who loves a carnations arrangement is directly left of the person who loves the vase of tulips
                carnations_house = None
                for house in assignment:
                    if house['flower'] == 'carnations':
                        carnations_house = house
                if not carnations_house or not tulips_house or carnations_house['house'] != tulips_house['house'] - 1:
                    valid = False
                    continue
                
                # Clue 10: The cat lover is not in the first house
                cat_house = None
                for house in assignment:
                    if house['animal'] == 'cat':
                        cat_house = house
                if not cat_house or cat_house['house'] == 1:
                    valid = False
                    continue
                
                if valid:
                    # Format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Flower", "Animal"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment, key=lambda x: x['house']):
                        solution["solution"]["rows"].append([
                            str(house['house']),
                            house['name'],
                            house['flower'],
                            house['animal']
                        ])
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()