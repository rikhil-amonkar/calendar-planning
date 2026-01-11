import itertools
import json

def is_valid_solution(house1, house2):
    # Unpack the attributes
    name1, sport1, hair1, height1, smoothie1, flower1 = house1
    name2, sport2, hair2, height2, smoothie2, flower2 = house2
    
    # Constraint 1: The person who loves soccer is not in the second house.
    if sport2 == 'soccer':
        return False
    
    # Constraint 2: The Desert smoothie lover is directly left of the person who is very short.
    if smoothie1 == 'desert' and height2 != 'very short':
        return False
    
    # Constraint 3: The person who is very short is the person who has brown hair.
    if height1 == 'very short' and hair1 != 'brown':
        return False
    if height2 == 'very short' and hair2 != 'brown':
        return False
    
    # Constraint 4: The person who loves a carnations arrangement is the Desert smoothie lover.
    if flower1 == 'carnations' and smoothie1 != 'desert':
        return False
    if flower2 == 'carnations' and smoothie2 != 'desert':
        return False
    
    # Constraint 5: Eric and the person who has brown hair are next to each other.
    if name1 == 'Eric' and hair2 != 'brown':
        return False
    if name2 == 'Eric' and hair1 != 'brown':
        return False
    
    return True

def solve_puzzle():
    # Define all possible attributes
    names = ['Arnold', 'Eric']
    sports = ['basketball', 'soccer']
    hair_colors = ['brown', 'black']
    heights = ['very short', 'short']
    smoothies = ['desert', 'cherry']
    flowers = ['daffodils', 'carnations']
    
    # Generate all possible combinations for one house
    all_combinations = list(itertools.permutations(names + sports + hair_colors + heights + smoothies + flowers, 6))
    
    # Filter down to only valid combinations for each house
    valid_combinations = []
    for comb in all_combinations:
        name, sport, hair, height, smoothie, flower = comb
        if len(set([name, sport, hair, height, smoothie, flower])) == 6:
            valid_combinations.append((name, sport, hair, height, smoothie, flower))
    
    # Try all pairings of valid combinations for the two houses
    for house1 in valid_combinations:
        for house2 in valid_combinations:
            if len(set(house1 + house2)) == 12 and is_valid_solution(house1, house2):
                # Format the solution as required
                solution = {
                    "solution": {
                        "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
                        "rows": [
                            ["1", house1[0], house1[1], house1[2], house1[3], house1[4], house1[5]],
                            ["2", house2[0], house2[1], house2[2], house2[3], house2[4], house2[5]]
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())