import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Arnold', 'Peter', 'Eric']
    animals = ['bird', 'horse', 'cat']
    months = ['jan', 'sept', 'april']
    hobbies = ['photography', 'cooking', 'gardening']
    drinks = ['milk', 'water', 'tea']
    hair_colors = ['black', 'brown', 'blonde']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for animal_perm in permutations(animals):
            for month_perm in permutations(months):
                for hobby_perm in permutations(hobbies):
                    for drink_perm in permutations(drinks):
                        for hair_perm in permutations(hair_colors):
                            # Assign each permutation to houses 1, 2, 3
                            solution = {
                                1: {
                                    'Name': name_perm[0],
                                    'animal': animal_perm[0],
                                    'month': month_perm[0],
                                    'hobby': hobby_perm[0],
                                    'drink': drink_perm[0],
                                    'hair_color': hair_perm[0]
                                },
                                2: {
                                    'Name': name_perm[1],
                                    'animal': animal_perm[1],
                                    'month': month_perm[1],
                                    'hobby': hobby_perm[1],
                                    'drink': drink_perm[1],
                                    'hair_color': hair_perm[1]
                                },
                                3: {
                                    'Name': name_perm[2],
                                    'animal': animal_perm[2],
                                    'month': month_perm[2],
                                    'hobby': hobby_perm[2],
                                    'drink': drink_perm[2],
                                    'hair_color': hair_perm[2]
                                }
                            }
                            
                            # Check all constraints
                            # 2. April is in the third house
                            if solution[3]['month'] != 'april':
                                continue
                            
                            # 3. Eric is not in the first house
                            if solution[1]['Name'] == 'Eric':
                                continue
                            
                            # 4. Cat lover is in the second house
                            if solution[2]['animal'] != 'cat':
                                continue
                            
                            # 7. Cat lover has brown hair
                            if solution[2]['hair_color'] != 'brown':
                                continue
                            
                            # 1. Brown hair loves cooking
                            for house in solution.values():
                                if house['hair_color'] == 'brown' and house['hobby'] != 'cooking':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # 5. Blonde is left of milk
                            blonde_pos = None
                            milk_pos = None
                            for house_num in [1, 2, 3]:
                                if solution[house_num]['hair_color'] == 'blonde':
                                    blonde_pos = house_num
                                if solution[house_num]['drink'] == 'milk':
                                    milk_pos = house_num
                            if blonde_pos is None or milk_pos is None or blonde_pos >= milk_pos:
                                continue
                            
                            # 6. Gardening likes milk
                            for house in solution.values():
                                if house['hobby'] == 'gardening' and house['drink'] != 'milk':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # 8. Arnold is the bird keeper
                            for house in solution.values():
                                if house['Name'] == 'Arnold' and house['animal'] != 'bird':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # 9. Water drinker is photography enthusiast
                            for house in solution.values():
                                if house['drink'] == 'water' and house['hobby'] != 'photography':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # 10. September is directly left of Arnold
                            sept_pos = None
                            arnold_pos = None
                            for house_num in [1, 2, 3]:
                                if solution[house_num]['month'] == 'sept':
                                    sept_pos = house_num
                                if solution[house_num]['Name'] == 'Arnold':
                                    arnold_pos = house_num
                            if sept_pos is None or arnold_pos is None or sept_pos + 1 != arnold_pos:
                                continue
                            
                            # If all constraints are satisfied, return the solution
                            output = {
                                "solution": {
                                    "header": ["House", "Name", "animal", "month", "hobby", "drink", "hair_color"],
                                    "rows": []
                                }
                            }
                            for house_num in [1, 2, 3]:
                                house = solution[house_num]
                                output["solution"]["rows"].append([
                                    str(house_num),
                                    house['Name'],
                                    house['animal'],
                                    house['month'],
                                    house['hobby'],
                                    house['drink'],
                                    house['hair_color']
                                ])
                            return output
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))