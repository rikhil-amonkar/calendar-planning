import itertools
import json

names_list = ['Arnold', 'Alice', 'Eric', 'Peter']
hobbies_list = ['cooking', 'painting', 'photography', 'gardening']
birthdays_list = ['april', 'jan', 'sept', 'feb']
education_list = ['master', 'bachelor', 'associate', 'high school']
smoothie_list = ['cherry', 'watermelon', 'desert', 'dragonfruit']

solution = None

for names in itertools.permutations(names_list):
    for hobbies in itertools.permutations(hobbies_list):
        for birthdays in itertools.permutations(birthdays_list):
            if birthdays[2] != 'sept':
                continue
            for educations in itertools.permutations(education_list):
                if educations[2] != 'high school':
                    continue
                for smoothies in itertools.permutations(smoothie_list):
                    # Constraint 1: Desert lover's birthday is jan
                    desert_index = smoothies.index('desert')
                    if birthdays[desert_index] != 'jan':
                        continue
                    # Constraint 2: Eric has bachelor
                    eric_index = names.index('Eric')
                    if educations[eric_index] != 'bachelor':
                        continue
                    # Constraint 3: jan birthday has bachelor
                    jan_index = birthdays.index('jan')
                    if educations[jan_index] != 'bachelor':
                        continue
                    # Constraint 5: Watermelon not in third house
                    if smoothies[2] == 'watermelon':
                        continue
                    # Constraint 6: Arnold has associate
                    arnold_index = names.index('Arnold')
                    if educations[arnold_index] != 'associate':
                        continue
                    # Constraint 7: master's has painting
                    master_index = educations.index('master')
                    if hobbies[master_index] != 'painting':
                        continue
                    # Constraint 8: one house between Dragonfruit and sept (house 2)
                    dragonfruit_index = smoothies.index('dragonfruit')
                    if abs(dragonfruit_index - 2) != 2:
                        continue
                    # Constraint 10: Alice's hobby is cooking
                    alice_index = names.index('Alice')
                    if hobbies[alice_index] != 'cooking':
                        continue
                    # Constraint 11: april and gardener adjacent
                    april_index = birthdays.index('april')
                    gardening_index = hobbies.index('gardening')
                    if abs(april_index - gardening_index) != 1:
                        continue
                    # Constraint 12: painter's birthday is feb
                    painting_index = hobbies.index('painting')
                    if birthdays[painting_index] != 'feb':
                        continue
                    
                    # All constraints passed
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                            "rows": []
                        }
                    }
                    for i in range(4):
                        house_num = str(i + 1)
                        row = [house_num, names[i], hobbies[i], birthdays[i], educations[i], smoothies[i]]
                        solution['solution']['rows'].append(row)
                    # Output as JSON
                    print(json.dumps(solution))
                    exit()