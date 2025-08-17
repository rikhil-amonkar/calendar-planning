import json
from itertools import permutations, product

def main():
    categories = {
        'names': ['Eric', 'Arnold', 'Peter'],
        'vacation': ['mountain', 'city', 'beach'],
        'height': ['very short', 'average', 'short'],
        'flower': ['carnations', 'daffodils', 'lilies'],
        'haircolor': ['brown', 'black', 'blonde'],
        'education': ['associate', 'bachelor', 'high school']
    }

    # Generate all permutations for each category
    perm_lists = []
    for key in categories:
        perm_lists.append(list(permutations(categories[key])))

    # Iterate through all possible combinations of permutations
    for combination in product(*perm_lists):
        names_perm, vacation_perm, height_perm, flower_perm, haircolor_perm, education_perm = combination

        # Clue 1: Peter has average height
        peter_index = names_perm.index('Peter')
        if height_perm[peter_index] != 'average':
            continue

        # Clue 2: Arnold loves daffodils
        arnold_index = names_perm.index('Arnold')
        if flower_perm[arnold_index] != 'daffodils':
            continue

        # Clue 3: very short not in second house (index 1)
        vs_index = height_perm.index('very short')
        if vs_index == 1:
            continue

        # Clue 4: beach in first house (index 0)
        if vacation_perm[0] != 'beach':
            continue

        # Clue 5: high school in third house (index 2)
        if education_perm[2] != 'high school':
            continue

        # Clue 6: short is to the right of very short
        vs_index = height_perm.index('very short')
        short_index = height_perm.index('short')
        if short_index <= vs_index:
            continue

        # Clue 7: lilies is Eric
        lilies_index = flower_perm.index('lilies')
        if names_perm[lilies_index] != 'Eric':
            continue

        # Clue 8: lilies has bachelor
        if education_perm[lilies_index] != 'bachelor':
            continue

        # Clue 9: city is to the right of Peter
        city_index = vacation_perm.index('city')
        peter_index = names_perm.index('Peter')
        if city_index <= peter_index:
            continue

        # Clue 10: blonde in third house (index 2)
        if haircolor_perm[2] != 'blonde':
            continue

        # Clue 11: beach vacation has brown hair
        beach_index = vacation_perm.index('beach')
        if haircolor_perm[beach_index] != 'brown':
            continue

        # If passed all checks, build the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                "rows": []
            }
        }

        for i in range(3):
            house_num = str(i + 1)
            row = [
                house_num,
                names_perm[i],
                vacation_perm[i],
                height_perm[i],
                flower_perm[i],
                haircolor_perm[i],
                education_perm[i]
            ]
            solution['solution']['rows'].append(row)

        print(json.dumps(solution))
        return

if __name__ == "__main__":
    main()