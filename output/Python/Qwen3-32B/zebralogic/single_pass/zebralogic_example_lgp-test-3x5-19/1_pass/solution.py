import itertools
import json

def main():
    names = ['Arnold', 'Peter', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    educations = ['associate', 'high school', 'bachelor']
    smoothies = ['desert', 'cherry', 'watermelon']
    hobbies = ['gardening', 'cooking', 'photography']

    for name_perm in itertools.permutations(names):
        for occu_perm in itertools.permutations(occupations):
            for edu_perm in itertools.permutations(educations):
                for smoothie_perm in itertools.permutations(smoothies):
                    for hobby_perm in itertools.permutations(hobbies):
                        # Clue 1: Desert smoothie lover is doctor
                        desert_index = smoothie_perm.index('desert')
                        if occu_perm[desert_index] != 'doctor':
                            continue

                        # Clue 2: Arnold is not in the third house
                        if name_perm[2] == 'Arnold':
                            continue

                        # Clue 3: Cherry smoothie is to the right of Peter
                        peter_index = name_perm.index('Peter')
                        cherry_index = smoothie_perm.index('cherry')
                        if cherry_index <= peter_index:
                            continue

                        # Clue 4: Cooking is in the second house
                        if hobby_perm[1] != 'cooking':
                            continue

                        # Clue 5: Cooking is Peter
                        cooking_index = hobby_perm.index('cooking')
                        if name_perm[cooking_index] != 'Peter':
                            continue

                        # Clue 6: Associate's degree is to the right of gardening
                        assoc_index = edu_perm.index('associate')
                        garden_index = hobby_perm.index('gardening')
                        if assoc_index <= garden_index:
                            continue

                        # Clue 7: Bachelor's degree is to the right of Desert smoothie
                        bachelor_index = edu_perm.index('bachelor')
                        desert_index = smoothie_perm.index('desert')
                        if bachelor_index <= desert_index:
                            continue

                        # Clue 8: Cooking lover is doctor
                        cooking_index = hobby_perm.index('cooking')
                        if occu_perm[cooking_index] != 'doctor':
                            continue

                        # Clue 9: Photography enthusiast is teacher
                        photo_index = hobby_perm.index('photography')
                        if occu_perm[photo_index] != 'teacher':
                            continue

                        # Build solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                                "rows": []
                            }
                        }
                        for i in range(3):
                            house_num = str(i + 1)
                            name = name_perm[i]
                            occupation = occu_perm[i]
                            education = edu_perm[i]
                            smoothie = smoothie_perm[i]
                            hobby = hobby_perm[i]
                            solution["solution"]["rows"].append([
                                house_num, name, occupation, education, smoothie, hobby
                            ])
                        print(json.dumps(solution))
                        return

if __name__ == "__main__":
    main()