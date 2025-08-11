import itertools
import json

def main():
    names = ['Eric', 'Arnold']
    mothers = ['Aniya', 'Holly']
    cars = ['ford f150', 'tesla model 3']
    heights = ['short', 'very short']
    
    all_name_perms = list(itertools.permutations(names))
    all_mother_perms = list(itertools.permutations(mothers))
    all_car_perms = list(itertools.permutations(cars))
    all_height_perms = list(itertools.permutations(heights))
    
    solution_found = None
    
    for n_perm in all_name_perms:
        for m_perm in all_mother_perms:
            for c_perm in all_car_perms:
                for h_perm in all_height_perms:
                    house1 = [n_perm[0], m_perm[0], c_perm[0], h_perm[0]]
                    house2 = [n_perm[1], m_perm[1], c_perm[1], h_perm[1]]
                    candidate = [house1, house2]
                    
                    if house2[1] != 'Holly':
                        continue
                    
                    arnold_short_ok = False
                    if house1[0] == 'Arnold':
                        if house1[3] == 'short':
                            arnold_short_ok = True
                        else:
                            continue
                    elif house2[0] == 'Arnold':
                        if house2[3] == 'short':
                            arnold_short_ok = True
                        else:
                            continue
                    else:
                        continue
                    
                    arnold_house = None
                    tesla_house = None
                    if house1[0] == 'Arnold':
                        arnold_house = 1
                    if house2[0] == 'Arnold':
                        arnold_house = 2
                    if house1[2] == 'tesla model 3':
                        tesla_house = 1
                    if house2[2] == 'tesla model 3':
                        tesla_house = 2
                    
                    if arnold_house is None or tesla_house is None:
                        continue
                    
                    if tesla_house <= arnold_house:
                        continue
                    
                    solution_found = candidate
                    break
                if solution_found is not None:
                    break
            if solution_found is not None:
                break
        if solution_found is not None:
            break
    
    if solution_found is None:
        result = {
            "solution": {
                "header": ["House", "Name", "Mother", "Car", "Height"],
                "rows": []
            }
        }
    else:
        rows = [
            ["1"] + solution_found[0],
            ["2"] + solution_found[1]
        ]
        result = {
            "solution": {
                "header": ["House", "Name", "Mother", "Car", "Height"],
                "rows": rows
            }
        }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()