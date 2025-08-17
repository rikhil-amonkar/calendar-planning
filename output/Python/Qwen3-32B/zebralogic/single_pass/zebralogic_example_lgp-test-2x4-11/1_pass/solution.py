import itertools
import json

# Generate all possible permutations for each category
names_list = ['Eric', 'Arnold']
hobbies_list = ['photography', 'gardening']
pets_list = ['cat', 'dog']
heights_list = ['very short', 'short']

solution_found = False

for names in itertools.permutations(names_list):
    for hobbies in itertools.permutations(hobbies_list):
        for pets in itertools.permutations(pets_list):
            for heights in itertools.permutations(heights_list):
                # Find the house with 'very short' height
                very_short_house = None
                for i, h in enumerate(heights):
                    if h == 'very short':
                        very_short_house = i + 1  # House numbers are 1-based
                        break
                
                # Check if the 'very short' person is Eric and has photography as hobby
                if very_short_house and names[very_short_house - 1] == 'Eric' and hobbies[very_short_house - 1] == 'photography':
                    # Find the house with the cat
                    cat_house = None
                    for i, pet in enumerate(pets):
                        if pet == 'cat':
                            cat_house = i + 1
                            break
                    
                    # Check if the cat is to the right of the 'very short' person
                    if cat_house and cat_house > very_short_house:
                        # Construct the solution rows
                        rows = []
                        for i in range(2):
                            house_num = i + 1
                            name = names[i]
                            hobby = hobbies[i]
                            pet = pets[i]
                            height = heights[i]
                            rows.append([str(house_num), name, hobby, pet, height])
                        
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                                "rows": rows
                            }
                        }
                        print(json.dumps(solution))
                        solution_found = True
                        break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break