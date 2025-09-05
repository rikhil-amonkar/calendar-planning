import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Arnold']
    smoothies = ['cherry', 'watermelon', 'desert']
    flowers = ['carnations', 'lilies', 'daffodils']
    animals = ['cat', 'horse', 'bird']
    hobbies = ['photography', 'cooking', 'gardening']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for flower_perm in permutations(flowers):
                for animal_perm in permutations(animals):
                    for hobby_perm in permutations(hobbies):
                        # Assign each permutation to houses 1, 2, 3
                        assignment = []
                        for i in range(3):
                            house = {
                                'House': str(i + 1),
                                'Name': name_perm[i],
                                'Smoothie': smoothie_perm[i],
                                'Flower': flower_perm[i],
                                'Animal': animal_perm[i],
                                'Hobby': hobby_perm[i]
                            }
                            assignment.append(house)
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
                        horse_houses = [h['House'] for h in assignment if h['Animal'] == 'horse']
                        photo_houses = [h['House'] for h in assignment if h['Hobby'] == 'photography']
                        if len(horse_houses) != 1 or len(photo_houses) != 1:
                            valid = False
                            continue
                        horse_house = int(horse_houses[0])
                        photo_house = int(photo_houses[0])
                        if abs(horse_house - photo_house) != 1:
                            valid = False
                            continue
                        
                        # Clue 2: The bird keeper is the person who likes Cherry smoothies.
                        bird_house = [h for h in assignment if h['Animal'] == 'bird'][0]
                        if bird_house['Smoothie'] != 'cherry':
                            valid = False
                            continue
                        
                        # Clue 3: The person who loves cooking is the Desert smoothie lover.
                        cooking_house = [h for h in assignment if h['Hobby'] == 'cooking'][0]
                        if cooking_house['Smoothie'] != 'desert':
                            valid = False
                            continue
                        
                        # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
                        gardening_house = [h for h in assignment if h['Hobby'] == 'gardening'][0]
                        if gardening_house['Flower'] != 'carnations':
                            valid = False
                            continue
                        
                        # Clue 5: The person who loves cooking is directly left of Peter.
                        peter_house = [h for h in assignment if h['Name'] == 'Peter'][0]
                        if int(cooking_house['House']) + 1 != int(peter_house['House']):
                            valid = False
                            continue
                        
                        # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
                        daffodil_house = [h for h in assignment if h['Flower'] == 'daffodils'][0]
                        if daffodil_house['Smoothie'] != 'desert':
                            valid = False
                            continue
                        
                        # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
                        watermelon_house = [h for h in assignment if h['Smoothie'] == 'watermelon'][0]
                        if watermelon_house['Animal'] != 'horse':
                            valid = False
                            continue
                        
                        # Clue 8: The photography enthusiast is Eric.
                        photo_enthusiast = [h for h in assignment if h['Hobby'] == 'photography'][0]
                        if photo_enthusiast['Name'] != 'Eric':
                            valid = False
                            continue
                        
                        if valid:
                            # Format the solution as required
                            header = ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"]
                            rows = []
                            for house in sorted(assignment, key=lambda x: int(x['House'])):
                                row = [
                                    house['House'],
                                    house['Name'],
                                    house['Smoothie'],
                                    house['Flower'],
                                    house['Animal'],
                                    house['Hobby']
                                ]
                                rows.append(row)
                            
                            result = {
                                "solution": {
                                    "header": header,
                                    "rows": rows
                                }
                            }
                            print(json.dumps(result, indent=2))
                            return
    
    print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()