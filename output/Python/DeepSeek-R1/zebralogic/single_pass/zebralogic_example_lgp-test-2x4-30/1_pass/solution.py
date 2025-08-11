import itertools
import json

def is_valid(candidate):
    arnold_house = None
    desert_house = None
    for i in range(2):
        if candidate[i]['Name'] == 'Arnold':
            arnold_house = i
        if candidate[i]['Favorite smoothie'] == 'desert':
            desert_house = i
    if arnold_house != desert_house:
        return False
        
    brown_house = None
    basketball_house = None
    for i in range(2):
        if candidate[i]['Hair color'] == 'brown':
            brown_house = i
        if candidate[i]['Favorite sport'] == 'basketball':
            basketball_house = i
    if brown_house != basketball_house:
        return False
        
    black_house = None
    for i in range(2):
        if candidate[i]['Hair color'] == 'black':
            black_house = i
    if arnold_house is None or black_house is None:
        return False
    if arnold_house >= black_house:
        return False
        
    return True

def main():
    names = ['Arnold', 'Eric']
    hairs = ['black', 'brown']
    sports = ['basketball', 'soccer']
    smoothies = ['desert', 'cherry']
    
    solution_candidate = None
    found = False
    for name_perm in itertools.permutations(names):
        for hair_perm in itertools.permutations(hairs):
            for sport_perm in itertools.permutations(sports):
                for smoothie_perm in itertools.permutations(smoothies):
                    candidate = [
                        {
                            'Name': name_perm[0],
                            'Hair color': hair_perm[0],
                            'Favorite sport': sport_perm[0],
                            'Favorite smoothie': smoothie_perm[0]
                        },
                        {
                            'Name': name_perm[1],
                            'Hair color': hair_perm[1],
                            'Favorite sport': sport_perm[1],
                            'Favorite smoothie': smoothie_perm[1]
                        }
                    ]
                    if is_valid(candidate):
                        solution_candidate = candidate
                        found = True
                        break
                if found:
                    break
            if found:
                break
        if found:
            break
            
    header = ["House", "Name", "Hair color", "Favorite sport", "Favorite smoothie"]
    rows = []
    if solution_candidate is not None:
        for idx in range(2):
            house = solution_candidate[idx]
            row = [str(idx+1), house['Name'], house['Hair color'], house['Favorite sport'], house['Favorite smoothie']]
            rows.append(row)
    else:
        rows = [['1', '?', '?', '?', '?'], ['2', '?', '?', '?', '?']]
        
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()