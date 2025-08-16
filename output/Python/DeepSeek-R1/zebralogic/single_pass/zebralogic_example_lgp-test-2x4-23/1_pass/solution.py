import itertools
import json

def main():
    names = ["Eric", "Arnold"]
    mothers = ["Aniya", "Holly"]
    cars = ["ford f150", "tesla model 3"]
    heights = ["short", "very short"]
    
    found = False
    solution_rows = None
    
    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for car_perm in itertools.permutations(cars):
                for height_perm in itertools.permutations(heights):
                    if mother_perm[1] != 'Holly':
                        continue
                    
                    arnold_house = None
                    if name_perm[0] == 'Arnold':
                        arnold_house = 1
                    elif name_perm[1] == 'Arnold':
                        arnold_house = 2
                    else:
                        continue
                    
                    tesla_house = None
                    if car_perm[0] == 'tesla model 3':
                        tesla_house = 1
                    elif car_perm[1] == 'tesla model 3':
                        tesla_house = 2
                    else:
                        continue
                    
                    if tesla_house <= arnold_house:
                        continue
                    
                    if arnold_house == 1:
                        if height_perm[0] != 'short':
                            continue
                    else:
                        if height_perm[1] != 'short':
                            continue
                    
                    solution_rows = [
                        ["1", name_perm[0], mother_perm[0], car_perm[0], height_perm[0]],
                        ["2", name_perm[1], mother_perm[1], car_perm[1], height_perm[1]]
                    ]
                    found = True
                    break
                if found:
                    break
            if found:
                break
        if found:
            break
    
    solution_dict = {
        "header": ["House", "Name", "Mother", "CarModel", "Height"],
        "rows": solution_rows
    }
    result = {"solution": solution_dict}
    print(json.dumps(result, separators=(',', ':')))

if __name__ == "__main__":
    main()