import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Arnold', 'Peter', 'Eric']
    animals = ['bird', 'horse', 'cat']
    birthdays = ['jan', 'sept', 'april']
    hobbies = ['photography', 'cooking', 'gardening']
    drinks = ['milk', 'water', 'tea']
    hair_colors = ['black', 'brown', 'blonde']
    
    # Generate all possible permutations for each house
    for name_perm in permutations(names):
        for animal_perm in permutations(animals):
            for birthday_perm in permutations(birthdays):
                for hobby_perm in permutations(hobbies):
                    for drink_perm in permutations(drinks):
                        for hair_perm in permutations(hair_colors):
                            # Assign each permutation to houses 1, 2, 3
                            assignment = {
                                1: {
                                    'Name': name_perm[0],
                                    'Animal': animal_perm[0],
                                    'Birthday': birthday_perm[0],
                                    'Hobby': hobby_perm[0],
                                    'Drink': drink_perm[0],
                                    'HairColor': hair_perm[0]
                                },
                                2: {
                                    'Name': name_perm[1],
                                    'Animal': animal_perm[1],
                                    'Birthday': birthday_perm[1],
                                    'Hobby': hobby_perm[1],
                                    'Drink': drink_perm[1],
                                    'HairColor': hair_perm[1]
                                },
                                3: {
                                    'Name': name_perm[2],
                                    'Animal': animal_perm[2],
                                    'Birthday': birthday_perm[2],
                                    'Hobby': hobby_perm[2],
                                    'Drink': drink_perm[2],
                                    'HairColor': hair_perm[2]
                                }
                            }
                            
                            # Check all constraints
                            # 1. The person who has brown hair is the person who loves cooking.
                            brown_hair_hobby = None
                            cooking_hair = None
                            for house in [1, 2, 3]:
                                if assignment[house]['HairColor'] == 'brown':
                                    brown_hair_hobby = assignment[house]['Hobby']
                                if assignment[house]['Hobby'] == 'cooking':
                                    cooking_hair = assignment[house]['HairColor']
                            if brown_hair_hobby != 'cooking' or cooking_hair != 'brown':
                                continue
                            
                            # 2. The person whose birthday is in April is in the third house.
                            if assignment[3]['Birthday'] != 'april':
                                continue
                            
                            # 3. Eric is not in the first house.
                            if assignment[1]['Name'] == 'Eric':
                                continue
                            
                            # 4. The cat lover is in the second house.
                            if assignment[2]['Animal'] != 'cat':
                                continue
                            
                            # 5. The person who has blonde hair is somewhere to the left of the person who likes milk.
                            blonde_house = None
                            milk_house = None
                            for house in [1, 2, 3]:
                                if assignment[house]['HairColor'] == 'blonde':
                                    blonde_house = house
                                if assignment[house]['Drink'] == 'milk':
                                    milk_house = house
                            if blonde_house is None or milk_house is None or blonde_house >= milk_house:
                                continue
                            
                            # 6. The person who enjoys gardening is the person who likes milk.
                            gardening_drink = None
                            milk_hobby = None
                            for house in [1, 2, 3]:
                                if assignment[house]['Hobby'] == 'gardening':
                                    gardening_drink = assignment[house]['Drink']
                                if assignment[house]['Drink'] == 'milk':
                                    milk_hobby = assignment[house]['Hobby']
                            if gardening_drink != 'milk' or milk_hobby != 'gardening':
                                continue
                            
                            # 7. The cat lover is the person who has brown hair.
                            if assignment[2]['HairColor'] != 'brown':
                                continue
                            
                            # 8. Arnold is the bird keeper.
                            arnold_animal = None
                            bird_keeper = None
                            for house in [1, 2, 3]:
                                if assignment[house]['Name'] == 'Arnold':
                                    arnold_animal = assignment[house]['Animal']
                                if assignment[house]['Animal'] == 'bird':
                                    bird_keeper = assignment[house]['Name']
                            if arnold_animal != 'bird' or bird_keeper != 'Arnold':
                                continue
                            
                            # 9. The one who only drinks water is the photography enthusiast.
                            water_hobby = None
                            photography_drink = None
                            for house in [1, 2, 3]:
                                if assignment[house]['Drink'] == 'water':
                                    water_hobby = assignment[house]['Hobby']
                                if assignment[house]['Hobby'] == 'photography':
                                    photography_drink = assignment[house]['Drink']
                            if water_hobby != 'photography' or photography_drink != 'water':
                                continue
                            
                            # 10. The person whose birthday is in September is directly left of Arnold.
                            sept_house = None
                            arnold_house = None
                            for house in [1, 2, 3]:
                                if assignment[house]['Birthday'] == 'sept':
                                    sept_house = house
                                if assignment[house]['Name'] == 'Arnold':
                                    arnold_house = house
                            if sept_house is None or arnold_house is None or sept_house + 1 != arnold_house:
                                continue
                            
                            # If we reach here, all constraints are satisfied
                            # Format the solution as required
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                                    "rows": [
                                        ["1", assignment[1]['Name'], assignment[1]['Animal'], assignment[1]['Birthday'], assignment[1]['Hobby'], assignment[1]['Drink'], assignment[1]['HairColor']],
                                        ["2", assignment[2]['Name'], assignment[2]['Animal'], assignment[2]['Birthday'], assignment[2]['Hobby'], assignment[2]['Drink'], assignment[2]['HairColor']],
                                        ["3", assignment[3]['Name'], assignment[3]['Animal'], assignment[3]['Birthday'], assignment[3]['Hobby'], assignment[3]['Drink'], assignment[3]['HairColor']]
                                    ]
                                }
                            }
                            
                            print(json.dumps(solution))
                            return
    
    # If no solution found (shouldn't happen with valid constraints)
    print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == "__main__":
    main()