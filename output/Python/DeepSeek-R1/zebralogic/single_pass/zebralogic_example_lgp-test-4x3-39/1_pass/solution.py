import itertools
import json

def main():
    names_list = ['Eric', 'Alice', 'Peter', 'Arnold']
    hairs_list = ['blonde', 'black', 'red', 'brown']
    sports_list = ['swimming', 'soccer', 'basketball', 'tennis']
    
    found = False
    solution_data = None
    
    for names_perm in itertools.permutations(names_list):
        for hairs_perm in itertools.permutations(hairs_list):
            red_index = None
            black_index = None
            for idx, color in enumerate(hairs_perm):
                if color == 'red':
                    red_index = idx
                if color == 'black':
                    black_index = idx
            if red_index is None or black_index is None:
                continue
            if black_index != red_index + 1:
                continue
            
            for sports_perm in itertools.permutations(sports_list):
                if sports_perm[1] == 'soccer':
                    continue
                
                eric_index = names_perm.index('Eric')
                if hairs_perm[eric_index] != 'blonde':
                    continue
                
                basketball_index = sports_perm.index('basketball')
                if eric_index <= basketball_index:
                    continue
                
                if sports_perm[black_index] != 'tennis':
                    continue
                
                arnold_index = names_perm.index('Arnold')
                if arnold_index >= red_index:
                    continue
                
                alice_index = names_perm.index('Alice')
                if sports_perm[alice_index] != 'swimming':
                    continue
                
                solution_data = (names_perm, hairs_perm, sports_perm)
                found = True
                break
            if found:
                break
        if found:
            break
    
    if found:
        rows = []
        for i in range(4):
            row = [str(i+1), solution_data[0][i], solution_data[1][i], solution_data[2][i]]
            rows.append(row)
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": rows
            }
        }
    else:
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": []
            }
        }
    
    print(json.dumps(solution_dict))

if __name__ == '__main__':
    main()