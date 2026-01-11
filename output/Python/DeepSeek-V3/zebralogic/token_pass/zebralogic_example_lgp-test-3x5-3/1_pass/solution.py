import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ["Eric", "Peter", "Arnold"]
    smoothies = ["cherry", "watermelon", "desert"]
    flowers = ["carnations", "lilies", "daffodils"]
    animals = ["cat", "horse", "bird"]
    hobbies = ["photography", "cooking", "gardening"]
    
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for flower_perm in permutations(flowers):
                for animal_perm in permutations(animals):
                    for hobby_perm in permutations(hobbies):
                        
                        # Create assignment dictionaries
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                'Name': name_perm[i],
                                'Smoothie': smoothie_perm[i],
                                'Flower': flower_perm[i],
                                'Animal': animal_perm[i],
                                'Hobby': hobby_perm[i]
                            }
                        
                        # Check all clues
                        valid = True
                        
                        # Clue 1: The person who keeps horses and the photography enthusiast are next to each other
                        horse_houses = [h for h in houses if assignment[h]['Animal'] == 'horse']
                        photo_houses = [h for h in houses if assignment[h]['Hobby'] == 'photography']
                        if len(horse_houses) != 1 or len(photo_houses) != 1:
                            valid = False
                        else:
                            if abs(horse_houses[0] - photo_houses[0]) != 1:
                                valid = False
                        
                        if not valid:
                            continue
                        
                        # Clue 2: The bird keeper is the person who likes Cherry smoothies
                        bird_house = [h for h in houses if assignment[h]['Animal'] == 'bird'][0]
                        if assignment[bird_house]['Smoothie'] != 'cherry':
                            continue
                        
                        # Clue 3: The person who loves cooking is the Desert smoothie lover
                        cooking_house = [h for h in houses if assignment[h]['Hobby'] == 'cooking'][0]
                        if assignment[cooking_house]['Smoothie'] != 'desert':
                            continue
                        
                        # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement
                        gardening_house = [h for h in houses if assignment[h]['Hobby'] == 'gardening'][0]
                        if assignment[gardening_house]['Flower'] != 'carnations':
                            continue
                        
                        # Clue 5: The person who loves cooking is directly left of Peter
                        peter_house = [h for h in houses if assignment[h]['Name'] == 'Peter'][0]
                        if cooking_house + 1 != peter_house:
                            continue
                        
                        # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover
                        daffodil_house = [h for h in houses if assignment[h]['Flower'] == 'daffodils'][0]
                        if assignment[daffodil_house]['Smoothie'] != 'desert':
                            continue
                        
                        # Clue 7: The Watermelon smoothie lover is the person who keeps horses
                        watermelon_house = [h for h in houses if assignment[h]['Smoothie'] == 'watermelon'][0]
                        if assignment[watermelon_house]['Animal'] != 'horse':
                            continue
                        
                        # Clue 8: The photography enthusiast is Eric
                        photo_house = [h for h in houses if assignment[h]['Hobby'] == 'photography'][0]
                        if assignment[photo_house]['Name'] != 'Eric':
                            continue
                        
                        # All clues satisfied - found solution
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                                "rows": []
                            }
                        }
                        
                        for house in houses:
                            row = [
                                str(house),
                                assignment[house]['Name'],
                                assignment[house]['Smoothie'],
                                assignment[house]['Flower'],
                                assignment[house]['Animal'],
                                assignment[house]['Hobby']
                            ]
                            result["solution"]["rows"].append(row)
                        
                        return result
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()