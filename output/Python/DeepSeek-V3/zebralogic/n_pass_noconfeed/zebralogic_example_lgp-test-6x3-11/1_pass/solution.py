import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
    hair_colors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
    heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']
    
    # Try all permutations of assignments
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            for height_perm in permutations(heights):
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'name': name_perm[i],
                        'hair': hair_perm[i],
                        'height': height_perm[i]
                    }
                
                # Check all constraints
                # 2. Alice is in the fourth house.
                if assignment[4]['name'] != 'Alice':
                    continue
                
                # 3. The person who is short is Arnold.
                short_arnold = True
                for house, attrs in assignment.items():
                    if attrs['height'] == 'short' and attrs['name'] != 'Arnold':
                        short_arnold = False
                        break
                    if attrs['name'] == 'Arnold' and attrs['height'] != 'short':
                        short_arnold = False
                        break
                if not short_arnold:
                    continue
                
                # 4. The person who is tall is in the sixth house.
                if assignment[6]['height'] != 'tall':
                    continue
                
                # 5. The person who has black hair is not in the fourth house.
                if assignment[4]['hair'] == 'black':
                    continue
                
                # 6. The person who has red hair is Eric.
                red_eric = True
                for house, attrs in assignment.items():
                    if attrs['hair'] == 'red' and attrs['name'] != 'Eric':
                        red_eric = False
                        break
                    if attrs['name'] == 'Eric' and attrs['hair'] != 'red':
                        red_eric = False
                        break
                if not red_eric:
                    continue
                
                # 8. The person who has blonde hair is Carol.
                blonde_carol = True
                for house, attrs in assignment.items():
                    if attrs['hair'] == 'blonde' and attrs['name'] != 'Carol':
                        blonde_carol = False
                        break
                    if attrs['name'] == 'Carol' and attrs['hair'] != 'blonde':
                        blonde_carol = False
                        break
                if not blonde_carol:
                    continue
                
                # 10. The person who is very short is in the fifth house.
                if assignment[5]['height'] != 'very short':
                    continue
                
                # 11. Bob is the person who has brown hair.
                bob_brown = True
                for house, attrs in assignment.items():
                    if attrs['name'] == 'Bob' and attrs['hair'] != 'brown':
                        bob_brown = False
                        break
                    if attrs['hair'] == 'brown' and attrs['name'] != 'Bob':
                        bob_brown = False
                        break
                if not bob_brown:
                    continue
                
                # 12. The person who has gray hair is in the third house.
                if assignment[3]['hair'] != 'gray':
                    continue
                
                # 13. The person who has blonde hair is the person who is very tall.
                blonde_very_tall = True
                for house, attrs in assignment.items():
                    if attrs['hair'] == 'blonde' and attrs['height'] != 'very tall':
                        blonde_very_tall = False
                        break
                    if attrs['height'] == 'very tall' and attrs['hair'] != 'blonde':
                        blonde_very_tall = False
                        break
                if not blonde_very_tall:
                    continue
                
                # 1. The person who has blonde hair is directly left of Bob.
                blonde_left_of_bob = False
                for house in range(1, 6):
                    if assignment[house]['hair'] == 'blonde' and assignment[house + 1]['name'] == 'Bob':
                        blonde_left_of_bob = True
                        break
                if not blonde_left_of_bob:
                    continue
                
                # 7. The person who is super tall is somewhere to the right of the person who has an average height.
                super_tall_right_of_average = False
                average_house = None
                super_tall_house = None
                for house, attrs in assignment.items():
                    if attrs['height'] == 'average':
                        average_house = house
                    if attrs['height'] == 'super tall':
                        super_tall_house = house
                if average_house and super_tall_house and super_tall_house > average_house:
                    super_tall_right_of_average = True
                if not super_tall_right_of_average:
                    continue
                
                # 9. There is one house between the person who has gray hair and the person who has red hair.
                gray_red_one_between = False
                gray_house = None
                red_house = None
                for house, attrs in assignment.items():
                    if attrs['hair'] == 'gray':
                        gray_house = house
                    if attrs['hair'] == 'red':
                        red_house = house
                if gray_house and red_house and abs(gray_house - red_house) == 2:
                    gray_red_one_between = True
                if not gray_red_one_between:
                    continue
                
                # If we reach here, all constraints are satisfied
                result = {
                    "solution": {
                        "header": ["House", "Name", "HairColor", "Height"],
                        "rows": []
                    }
                }
                
                for house in sorted(assignment.keys()):
                    attrs = assignment[house]
                    result["solution"]["rows"].append([
                        str(house),
                        attrs['name'],
                        attrs['hair'],
                        attrs['height']
                    ])
                
                return result
    
    return {"solution": {"header": ["House", "Name", "HairColor", "Height"], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))