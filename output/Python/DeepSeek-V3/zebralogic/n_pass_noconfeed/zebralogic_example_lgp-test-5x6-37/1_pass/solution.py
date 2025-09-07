import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric']
    hobbies = ['cooking', 'gardening', 'painting', 'photography', 'knitting']
    sports = ['swimming', 'tennis', 'soccer', 'baseball', 'basketball']
    house_styles = ['ranch', 'craftsman', 'victorian', 'modern', 'colonial']
    children = ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all permutations for each category
    for name_perm in permutations(names):
        for hobby_perm in permutations(hobbies):
            for sport_perm in permutations(sports):
                for style_perm in permutations(house_styles):
                    for child_perm in permutations(children):
                        for height_perm in permutations(heights):
                            # Create assignment dictionaries
                            assignment = {}
                            for i, house in enumerate(houses):
                                assignment[house] = {
                                    'Name': name_perm[i],
                                    'Hobby': hobby_perm[i],
                                    'FavoriteSport': sport_perm[i],
                                    'HouseStyle': style_perm[i],
                                    'Children': child_perm[i],
                                    'Height': height_perm[i]
                                }
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: The person who has an average height is the person's child is named Meredith.
                            for house in houses:
                                if assignment[house]['Height'] == 'average':
                                    if assignment[house]['Children'] != 'Meredith':
                                        valid = False
                                    break
                            
                            # Clue 2: The person who is tall is in the second house.
                            if assignment[2]['Height'] != 'tall':
                                valid = False
                            
                            # Clue 3: Peter is directly left of the person residing in a Victorian house.
                            peter_house = None
                            victorian_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Peter':
                                    peter_house = house
                                if assignment[house]['HouseStyle'] == 'victorian':
                                    victorian_house = house
                            
                            if peter_house is None or victorian_house is None or peter_house + 1 != victorian_house:
                                valid = False
                            
                            # Clue 4: Alice is the person who is tall.
                            alice_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Alice':
                                    alice_house = house
                                    break
                            
                            if alice_house is None or assignment[alice_house]['Height'] != 'tall':
                                valid = False
                            
                            # Clue 5: The person who loves baseball is the person who is very tall.
                            for house in houses:
                                if assignment[house]['FavoriteSport'] == 'baseball':
                                    if assignment[house]['Height'] != 'very tall':
                                        valid = False
                                    break
                            
                            # Clue 6: The person's child is named Meredith and the person who is the mother of Timothy are next to each other.
                            meredith_house = None
                            timothy_house = None
                            for house in houses:
                                if assignment[house]['Children'] == 'Meredith':
                                    meredith_house = house
                                if assignment[house]['Children'] == 'Timothy':
                                    timothy_house = house
                            
                            if meredith_house is None or timothy_house is None or abs(meredith_house - timothy_house) != 1:
                                valid = False
                            
                            # Clue 7: Bob is the person who paints as a hobby.
                            for house in houses:
                                if assignment[house]['Name'] == 'Bob':
                                    if assignment[house]['Hobby'] != 'painting':
                                        valid = False
                                    break
                            
                            # Clue 8: The person who enjoys gardening is in the second house.
                            if assignment[2]['Hobby'] != 'gardening':
                                valid = False
                            
                            # Clue 9: The person who is very short is somewhere to the right of Eric.
                            eric_house = None
                            very_short_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Eric':
                                    eric_house = house
                                if assignment[house]['Height'] == 'very short':
                                    very_short_house = house
                            
                            if eric_house is None or very_short_house is None or very_short_house <= eric_house:
                                valid = False
                            
                            # Clue 10: The person who loves tennis is the person's child is named Samantha.
                            for house in houses:
                                if assignment[house]['FavoriteSport'] == 'tennis':
                                    if assignment[house]['Children'] != 'Samantha':
                                        valid = False
                                    break
                            
                            # Clue 11: The person who loves soccer is not in the first house.
                            if assignment[1]['FavoriteSport'] == 'soccer':
                                valid = False
                            
                            # Clue 12: The person's child is named Samantha is the person in a modern-style house.
                            for house in houses:
                                if assignment[house]['Children'] == 'Samantha':
                                    if assignment[house]['HouseStyle'] != 'modern':
                                        valid = False
                                    break
                            
                            # Clue 13: The person in a Craftsman-style house is the person who has an average height.
                            for house in houses:
                                if assignment[house]['HouseStyle'] == 'craftsman':
                                    if assignment[house]['Height'] != 'average':
                                        valid = False
                                    break
                            
                            # Clue 14: The person's child is named Fred is the person residing in a Victorian house.
                            for house in houses:
                                if assignment[house]['Children'] == 'Fred':
                                    if assignment[house]['HouseStyle'] != 'victorian':
                                        valid = False
                                    break
                            
                            # Clue 15: The person who is short is the person who loves basketball.
                            for house in houses:
                                if assignment[house]['Height'] == 'short':
                                    if assignment[house]['FavoriteSport'] != 'basketball':
                                        valid = False
                                    break
                            
                            # Clue 16: Peter is the person who is very tall.
                            if peter_house is not None and assignment[peter_house]['Height'] != 'very tall':
                                valid = False
                            
                            # Clue 17: The person in a ranch-style home is somewhere to the left of the person who loves cooking.
                            ranch_house = None
                            cooking_house = None
                            for house in houses:
                                if assignment[house]['HouseStyle'] == 'ranch':
                                    ranch_house = house
                                if assignment[house]['Hobby'] == 'cooking':
                                    cooking_house = house
                            
                            if ranch_house is None or cooking_house is None or ranch_house >= cooking_house:
                                valid = False
                            
                            # Clue 18: The person who enjoys knitting and the person who enjoys gardening are next to each other.
                            knitting_house = None
                            gardening_house = None
                            for house in houses:
                                if assignment[house]['Hobby'] == 'knitting':
                                    knitting_house = house
                                if assignment[house]['Hobby'] == 'gardening':
                                    gardening_house = house
                            
                            if knitting_house is None or gardening_house is None or abs(knitting_house - gardening_house) != 1:
                                valid = False
                            
                            # Clue 19: The person in a modern-style house is the person who loves cooking.
                            for house in houses:
                                if assignment[house]['HouseStyle'] == 'modern':
                                    if assignment[house]['Hobby'] != 'cooking':
                                        valid = False
                                    break
                            
                            # Clue 20: The person residing in a Victorian house is in the fifth house.
                            if assignment[5]['HouseStyle'] != 'victorian':
                                valid = False
                            
                            if valid:
                                # Found the solution
                                result = {
                                    "solution": {
                                        "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
                                        "rows": []
                                    }
                                }
                                
                                for house in houses:
                                    row = [
                                        str(house),
                                        assignment[house]['Name'],
                                        assignment[house]['Hobby'],
                                        assignment[house]['FavoriteSport'],
                                        assignment[house]['HouseStyle'],
                                        assignment[house]['Children'],
                                        assignment[house]['Height']
                                    ]
                                    result["solution"]["rows"].append(row)
                                
                                print(json.dumps(result, indent=2))
                                return
    
    print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()