import itertools
import json

def satisfies_constraints(names, heights, mothers, hairs):
    try:
        if heights.index('tall') != mothers.index('Holly'):
            return False
    except ValueError:
        return False

    found = False
    for i in range(4):
        if hairs[i] == 'gray' and mothers[i+1] == 'Janelle':
            found = True
            break
    if not found:
        return False

    if hairs[3] == 'black':
        return False

    eric_index = names.index('Eric')
    if hairs[eric_index] != 'black':
        return False

    try:
        if heights.index('very short') != mothers.index('Penny'):
            return False
    except ValueError:
        return False

    gray_index = hairs.index('gray')
    eric_index = names.index('Eric')
    if abs(eric_index - gray_index) != 1:
        return False

    peter_index = names.index('Peter')
    if hairs[peter_index] != 'red':
        return False

    arnold_index = names.index('Arnold')
    if hairs[arnold_index] != 'brown':
        return False

    janelle_index = mothers.index('Janelle')
    brown_index = hairs.index('brown')
    if brown_index >= janelle_index:
        return False

    aniya_index = mothers.index('Aniya')
    very_short_index = heights.index('very short')
    if abs(aniya_index - very_short_index) != 1:
        return False

    return True

def main():
    names_base = ['Alice', 'Peter', 'Eric', 'Arnold']
    heights_base = ['very short', 'tall', 'very tall']
    mothers_base = ['Janelle', 'Penny', 'Holly', 'Aniya']
    hairs_base = ['blonde', 'black', 'gray', 'red', 'brown']

    for name_perm in itertools.permutations(names_base):
        names = list(name_perm)
        names.append('Bob')

        for height_perm in itertools.permutations(heights_base):
            heights = [
                'average',
                height_perm[0],
                height_perm[1],
                'short',
                height_perm[2]
            ]

            for mother_perm in itertools.permutations(mothers_base):
                mothers = [
                    mother_perm[0],
                    mother_perm[1],
                    'Kailyn',
                    mother_perm[2],
                    mother_perm[3]
                ]

                for hair_perm in itertools.permutations(hairs_base):
                    hairs = list(hair_perm)

                    if satisfies_constraints(names, heights, mothers, hairs):
                        rows = []
                        for i in range(5):
                            rows.append([
                                str(i+1),
                                names[i],
                                heights[i],
                                mothers[i],
                                hairs[i]
                            ])
                        solution_dict = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Mother", "Hair"],
                                "rows": rows
                            }
                        }
                        print(json.dumps(solution_dict))
                        return

    print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()