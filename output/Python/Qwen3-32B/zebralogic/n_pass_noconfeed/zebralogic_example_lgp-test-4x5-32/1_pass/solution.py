import itertools
import json

def main():
    names_list = ['Arnold', 'Alice', 'Eric', 'Peter']
    hobbies_list = ['cooking', 'painting', 'photography', 'gardening']
    birthdays_list = ['april', 'jan', 'sept', 'feb']
    education_list = ['master', 'bachelor', 'associate', 'high school']
    smoothies_list = ['cherry', 'watermelon', 'desert', 'dragonfruit']

    for names_p in itertools.permutations(names_list):
        for hobbies_p in itertools.permutations(hobbies_list):
            for birthdays_p in itertools.permutations(birthdays_list):
                if birthdays_p[2] != 'sept':
                    continue  # clue 9
                for education_p in itertools.permutations(education_list):
                    if education_p[2] != 'high school':
                        continue  # clue 4
                    for smoothies_p in itertools.permutations(smoothies_list):
                        if smoothies_p[0] != 'dragonfruit':
                            continue  # clue 8
                        if is_valid(names_p, hobbies_p, birthdays_p, education_p, smoothies_p):
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                                    "rows": []
                                }
                            }
                            for i in range(4):
                                house_num = str(i + 1)
                                row = [
                                    house_num,
                                    names_p[i],
                                    hobbies_p[i],
                                    birthdays_p[i],
                                    education_p[i],
                                    smoothies_p[i]
                                ]
                                solution['solution']['rows'].append(row)
                            print(json.dumps(solution))
                            return

def is_valid(names_p, hobbies_p, birthdays_p, education_p, smoothies_p):
    # Check clue 1: desert smoothie lover has jan birthday
    desert_index = smoothies_p.index('desert')
    if birthdays_p[desert_index] != 'jan':
        return False

    # Check clue 2: Eric has bachelor
    eric_index = names_p.index('Eric')
    if education_p[eric_index] != 'bachelor':
        return False

    # Check clue 3: jan birthday has bachelor
    jan_index = birthdays_p.index('jan')
    if education_p[jan_index] != 'bachelor':
        return False

    # Check clue 5: watermelon not in third house
    if smoothies_p[2] == 'watermelon':
        return False

    # Check clue 6: Arnold has associate
    arnold_index = names_p.index('Arnold')
    if education_p[arnold_index] != 'associate':
        return False

    # Check clue 7: master's degree person paints
    master_index = education_p.index('master')
    if hobbies_p[master_index] != 'painting':
        return False

    # Check clue 10: cooking is Alice
    cooking_index = hobbies_p.index('cooking')
    if names_p[cooking_index] != 'Alice':
        return False

    # Check clue 11: april birthday and gardener are adjacent
    april_index = birthdays_p.index('april')
    gardening_index = hobbies_p.index('gardening')
    if abs(april_index - gardening_index) != 1:
        return False

    # Check clue 12: painter's birthday is feb
    painting_index = hobbies_p.index('painting')
    if birthdays_p[painting_index] != 'feb':
        return False

    return True

if __name__ == "__main__":
    main()