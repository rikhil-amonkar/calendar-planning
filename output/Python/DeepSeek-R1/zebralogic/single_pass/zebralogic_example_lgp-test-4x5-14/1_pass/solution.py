import itertools
import json

def main():
    names_list = ['Peter', 'Eric', 'Arnold']
    mothers_list = ['Holly', 'Aniya', 'Kailyn']
    heights_list = ['very short', 'average', 'short']
    smoothies_list = ['watermelon', 'dragonfruit', 'desert', 'cherry']
    educations_list = ['high school', 'associate', 'master', 'bachelor']
    
    found = None
    for nc in itertools.permutations(names_list):
        for mc in itertools.permutations(mothers_list):
            for hc in itertools.permutations(heights_list):
                for sc in itertools.permutations(smoothies_list):
                    for ec in itertools.permutations(educations_list):
                        names_arr = [nc[0], nc[1], 'Alice', nc[2]]
                        mothers_arr = [mc[0], mc[1], 'Janelle', mc[2]]
                        heights_arr = [hc[0], hc[1], 'tall', hc[2]]
                        smoothies_arr = list(sc)
                        educations_arr = list(ec)
                        
                        if not check_constraints(names_arr, mothers_arr, smoothies_arr, heights_arr, educations_arr):
                            continue
                        found = (names_arr, mothers_arr, smoothies_arr, heights_arr, educations_arr)
                        break
                    if found: break
                if found: break
            if found: break
        if found: break
    
    if found is None:
        print(json.dumps({"solution": {}}))
        return
    
    rows = []
    for i in range(4):
        rows.append([str(i+1), found[0][i], found[1][i], found[2][i], found[3][i], found[4][i]])
    
    solution = {
        "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
        "rows": rows
    }
    output = {"solution": solution}
    print(json.dumps(output))

def check_constraints(names_arr, mothers_arr, smoothies_arr, heights_arr, educations_arr):
    # Clue 2: Desert smoothie lover has master's degree
    try:
        idx_desert = smoothies_arr.index('desert')
        if educations_arr[idx_desert] != 'master':
            return False
    except ValueError:
        return False
    
    # Clue 3: Desert smoothie not in first house
    if smoothies_arr[0] == 'desert':
        return False
    
    # Clue 4: Very short is left of high school
    try:
        idx_very_short = heights_arr.index('very short')
        idx_high_school = educations_arr.index('high school')
        if idx_very_short >= idx_high_school:
            return False
    except ValueError:
        return False
    
    # Clue 5: Eric and Cherry smoothie are adjacent
    try:
        idx_eric = names_arr.index('Eric')
        idx_cherry = smoothies_arr.index('cherry')
        if abs(idx_eric - idx_cherry) != 1:
            return False
    except ValueError:
        return False
    
    # Clue 6: High school diploma not in third house
    if educations_arr[2] == 'high school':
        return False
    
    # Clue 7: Mother Kailyn has associate degree
    try:
        idx_kailyn = mothers_arr.index('Kailyn')
        if educations_arr[idx_kailyn] != 'associate':
            return False
    except ValueError:
        return False
    
    # Clue 8: Cherry smoothie lover has mother Aniya
    try:
        idx_cherry = smoothies_arr.index('cherry')
        if mothers_arr[idx_cherry] != 'Aniya':
            return False
    except ValueError:
        return False
    
    # Clue 10: Arnold is right of average height
    try:
        idx_average = heights_arr.index('average')
        idx_arnold = names_arr.index('Arnold')
        if idx_average >= idx_arnold:
            return False
    except ValueError:
        return False
    
    # Clue 11: Dragonfruit smoothie directly left of short
    try:
        idx_dragon = smoothies_arr.index('dragonfruit')
        idx_short = heights_arr.index('short')
        if idx_dragon != idx_short - 1:
            return False
    except ValueError:
        return False
    
    return True

if __name__ == '__main__':
    main()