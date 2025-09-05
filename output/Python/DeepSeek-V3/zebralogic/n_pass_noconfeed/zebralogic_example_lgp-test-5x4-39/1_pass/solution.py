import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob']
    hobbies = ['painting', 'cooking', 'knitting', 'gardening', 'photography']
    heights = ['very tall', 'tall', 'very short', 'average', 'short']
    foods = ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations for each category
    name_perms = list(permutations(names))
    hobby_perms = list(permutations(hobbies))
    height_perms = list(permutations(heights))
    food_perms = list(permutations(foods))
    
    # Try all combinations to find the solution
    for name_assignment in name_perms:
        # Check clue 3: Peter is not in the second house
        if name_assignment[1] == 'Peter':
            continue
            
        # Check clue 8: Eric is not in the fifth house
        if name_assignment[4] == 'Eric':
            continue
            
        for hobby_assignment in hobby_perms:
            # Check clue 1: Bob is the photography enthusiast
            bob_index = name_assignment.index('Bob')
            if hobby_assignment[bob_index] != 'photography':
                continue
                
            for height_assignment in height_perms:
                # Check clue 9: The person who is short is Peter
                peter_index = name_assignment.index('Peter')
                if height_assignment[peter_index] != 'short':
                    continue
                    
                # Check clue 12: The person who is very short is in the fifth house
                if height_assignment[4] != 'very short':
                    continue
                    
                # Check clue 13: The person who is tall is in the third house
                if height_assignment[2] != 'tall':
                    continue
                    
                # Check clue 5: The person who loves cooking is the person who has an average height
                cooking_index = hobby_assignment.index('cooking')
                if height_assignment[cooking_index] != 'average':
                    continue
                    
                for food_assignment in food_perms:
                    # Check clue 2: The person who loves eating grilled cheese is the person who is tall
                    grilled_cheese_index = food_assignment.index('grilled cheese')
                    if height_assignment[grilled_cheese_index] != 'tall':
                        continue
                        
                    # Check clue 4: The person who is tall is directly left of the person who loves stir fry
                    tall_index = height_assignment.index('tall')
                    if tall_index >= 4 or food_assignment[tall_index + 1] != 'stir fry':
                        continue
                        
                    # Check clue 6: Alice is directly left of the person who is a pizza lover
                    alice_index = name_assignment.index('Alice')
                    if alice_index >= 4 or food_assignment[alice_index + 1] != 'pizza':
                        continue
                        
                    # Check clue 7: The person who loves the spaghetti eater is not in the second house
                    spaghetti_index = food_assignment.index('spaghetti')
                    if spaghetti_index == 1:
                        continue
                        
                    # Check clue 10: The person who has an average height and the person who enjoys gardening are next to each other
                    average_height_index = height_assignment.index('average')
                    gardening_index = hobby_assignment.index('gardening')
                    if abs(average_height_index - gardening_index) != 1:
                        continue
                        
                    # Check clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese
                    painting_index = hobby_assignment.index('painting')
                    if painting_index >= 4 or food_assignment[painting_index + 1] != 'grilled cheese':
                        continue
                        
                    # Check clue 14: Alice is somewhere to the right of the photography enthusiast
                    alice_index = name_assignment.index('Alice')
                    photography_index = hobby_assignment.index('photography')
                    if alice_index <= photography_index:
                        continue
                        
                    # If we reach here, we found a valid solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Hobby", "Height", "Food"],
                            "rows": []
                        }
                    }
                    
                    for i in range(5):
                        solution["solution"]["rows"].append([
                            str(i + 1),
                            name_assignment[i],
                            hobby_assignment[i],
                            height_assignment[i],
                            food_assignment[i]
                        ])
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    print('{"solution": {"header": ["House", "Name", "Hobby", "Height", "Food"], "rows": []}}')

if __name__ == "__main__":
    main()