import json
from itertools import permutations

def solve():
    # Define all possible values for each category
    names = ["Arnold", "Eric", "Peter"]
    flowers = ["carnations", "lilies", "daffodils"]
    hair_colors = ["black", "brown", "blonde"]
    sports = ["soccer", "basketball", "tennis"]
    house_styles = ["colonial", "ranch", "victorian"]
    pets = ["fish", "dog", "cat"]
    
    houses = [1, 2, 3]
    
    # Generate all permutations for each category across 3 houses
    for name_perm in permutations(names, 3):
        for flower_perm in permutations(flowers, 3):
            for hair_perm in permutations(hair_colors, 3):
                for sport_perm in permutations(sports, 3):
                    for style_perm in permutations(house_styles, 3):
                        for pet_perm in permutations(pets, 3):
                            
                            # Create assignment dictionaries
                            assignment = {}
                            for i in range(3):
                                assignment[i] = {
                                    'house': i+1,
                                    'name': name_perm[i],
                                    'flower': flower_perm[i],
                                    'hair': hair_perm[i],
                                    'sport': sport_perm[i],
                                    'style': style_perm[i],
                                    'pet': pet_perm[i]
                                }
                            
                            # Check all clues
                            # 1. The person who has a cat is the person who loves soccer.
                            cat_person = None
                            soccer_person = None
                            for i in range(3):
                                if assignment[i]['pet'] == 'cat':
                                    cat_person = i
                                if assignment[i]['sport'] == 'soccer':
                                    soccer_person = i
                            if cat_person != soccer_person:
                                continue
                            
                            # 2. The person who has blonde hair is in the second house.
                            if assignment[1]['hair'] != 'blonde':
                                continue
                            
                            # 3. The person who loves a bouquet of daffodils is the person who has blonde hair.
                            daffodil_person = None
                            for i in range(3):
                                if assignment[i]['flower'] == 'daffodils':
                                    daffodil_person = i
                            if daffodil_person != 1:  # blonde is in house 2
                                continue
                            
                            # 4. Peter is the person who loves basketball.
                            peter_person = None
                            basketball_person = None
                            for i in range(3):
                                if assignment[i]['name'] == 'Peter':
                                    peter_person = i
                                if assignment[i]['sport'] == 'basketball':
                                    basketball_person = i
                            if peter_person != basketball_person:
                                continue
                            
                            # 5. Arnold is directly left of the person in a ranch-style home.
                            arnold_person = None
                            ranch_person = None
                            for i in range(3):
                                if assignment[i]['name'] == 'Arnold':
                                    arnold_person = i
                                if assignment[i]['style'] == 'ranch':
                                    ranch_person = i
                            if ranch_person != arnold_person + 1:
                                continue
                            
                            # 6. The person who owns a dog is the person who loves basketball.
                            dog_person = None
                            for i in range(3):
                                if assignment[i]['pet'] == 'dog':
                                    dog_person = i
                            if dog_person != basketball_person:
                                continue
                            
                            # 7. The person who loves a carnations arrangement is directly left of the person who has blonde hair.
                            carnation_person = None
                            for i in range(3):
                                if assignment[i]['flower'] == 'carnations':
                                    carnation_person = i
                            if carnation_person != 0:  # must be in house 1 (left of house 2)
                                continue
                            
                            # 8. The person who loves soccer is in the third house.
                            if soccer_person != 2:
                                continue
                            
                            # 9. Arnold is somewhere to the left of the person who has black hair.
                            black_hair_person = None
                            for i in range(3):
                                if assignment[i]['hair'] == 'black':
                                    black_hair_person = i
                            if arnold_person >= black_hair_person:
                                continue
                            
                            # 10. The person living in a colonial-style house is in the third house.
                            if assignment[2]['style'] != 'colonial':
                                continue
                            
                            # All constraints satisfied - found solution
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                                    "rows": []
                                }
                            }
                            
                            for i in range(3):
                                row = [
                                    str(assignment[i]['house']),
                                    assignment[i]['name'],
                                    assignment[i]['flower'],
                                    assignment[i]['hair'],
                                    assignment[i]['sport'],
                                    assignment[i]['style'],
                                    assignment[i]['pet']
                                ]
                                result["solution"]["rows"].append(row)
                            
                            return result
    
    return None

if __name__ == "__main__":
    solution = solve()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))