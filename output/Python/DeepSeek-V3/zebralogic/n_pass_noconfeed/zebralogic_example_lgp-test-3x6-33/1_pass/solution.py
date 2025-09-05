import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Arnold', 'Eric', 'Peter']
    flowers = ['carnations', 'lilies', 'daffodils']
    hair_colors = ['black', 'brown', 'blonde']
    sports = ['soccer', 'basketball', 'tennis']
    house_styles = ['colonial', 'ranch', 'victorian']
    pets = ['fish', 'dog', 'cat']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for flower_perm in permutations(flowers):
            for hair_perm in permutations(hair_colors):
                for sport_perm in permutations(sports):
                    for style_perm in permutations(house_styles):
                        for pet_perm in permutations(pets):
                            # Assign houses 1, 2, 3
                            assignment = []
                            for i in range(3):
                                house = {
                                    'House': str(i+1),
                                    'Name': name_perm[i],
                                    'Flower': flower_perm[i],
                                    'HairColor': hair_perm[i],
                                    'FavoriteSport': sport_perm[i],
                                    'HouseStyle': style_perm[i],
                                    'Pet': pet_perm[i]
                                }
                                assignment.append(house)
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: The person who has a cat is the person who loves soccer.
                            cat_owner = next((h for h in assignment if h['Pet'] == 'cat'), None)
                            soccer_lover = next((h for h in assignment if h['FavoriteSport'] == 'soccer'), None)
                            if cat_owner != soccer_lover:
                                valid = False
                            
                            # Clue 2: The person who has blonde hair is in the second house.
                            if assignment[1]['HairColor'] != 'blonde':
                                valid = False
                            
                            # Clue 3: The person who loves a bouquet of daffodils is the person who has blonde hair.
                            daffodil_lover = next((h for h in assignment if h['Flower'] == 'daffodils'), None)
                            blonde_hair = next((h for h in assignment if h['HairColor'] == 'blonde'), None)
                            if daffodil_lover != blonde_hair:
                                valid = False
                            
                            # Clue 4: Peter is the person who loves basketball.
                            peter = next((h for h in assignment if h['Name'] == 'Peter'), None)
                            basketball_lover = next((h for h in assignment if h['FavoriteSport'] == 'basketball'), None)
                            if peter != basketball_lover:
                                valid = False
                            
                            # Clue 5: Arnold is directly left of the person in a ranch-style home.
                            arnold = next((h for h in assignment if h['Name'] == 'Arnold'), None)
                            ranch_house = next((h for h in assignment if h['HouseStyle'] == 'ranch'), None)
                            if not (arnold and ranch_house and int(arnold['House']) + 1 == int(ranch_house['House'])):
                                valid = False
                            
                            # Clue 6: The person who owns a dog is the person who loves basketball.
                            dog_owner = next((h for h in assignment if h['Pet'] == 'dog'), None)
                            if dog_owner != basketball_lover:
                                valid = False
                            
                            # Clue 7: The person who loves a carnations arrangement is directly left of the person who has blonde hair.
                            carnation_lover = next((h for h in assignment if h['Flower'] == 'carnations'), None)
                            if not (carnation_lover and blonde_hair and int(carnation_lover['House']) + 1 == int(blonde_hair['House'])):
                                valid = False
                            
                            # Clue 8: The person who loves soccer is in the third house.
                            if assignment[2]['FavoriteSport'] != 'soccer':
                                valid = False
                            
                            # Clue 9: Arnold is somewhere to the left of the person who has black hair.
                            black_hair = next((h for h in assignment if h['HairColor'] == 'black'), None)
                            if not (arnold and black_hair and int(arnold['House']) < int(black_hair['House'])):
                                valid = False
                            
                            # Clue 10: The person living in a colonial-style house is in the third house.
                            if assignment[2]['HouseStyle'] != 'colonial':
                                valid = False
                            
                            if valid:
                                # Format the solution as required
                                header = ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"]
                                rows = []
                                for house in sorted(assignment, key=lambda x: int(x['House'])):
                                    row = [
                                        house['House'],
                                        house['Name'],
                                        house['Flower'],
                                        house['HairColor'],
                                        house['FavoriteSport'],
                                        house['HouseStyle'],
                                        house['Pet']
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