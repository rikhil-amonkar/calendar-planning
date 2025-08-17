import itertools
import json

def solve_puzzle():
    names = ['Eric', 'Arnold']
    mothers = ['Aniya', 'Holly']
    cars = ['ford f150', 'tesla model 3']
    heights = ['short', 'very short']
    
    name_perms = list(itertools.permutations(names))
    mother_perms = list(itertools.permutations(mothers))
    car_perms = list(itertools.permutations(cars))
    height_perms = list(itertools.permutations(heights))
    
    for perm in itertools.product(name_perms, mother_perms, car_perms, height_perms):
        name_p, mother_p, car_p, height_p = perm
        
        # Check clue 3: Mother Holly in second house
        if mother_p[1] != 'Holly':
            continue
        
        # Find Arnold's index
        arnold_index = None
        for i, name in enumerate(name_p):
            if name == 'Arnold':
                arnold_index = i
                break
        
        # Check clue 2: Arnold is short
        if height_p[arnold_index] != 'short':
            continue
        
        # Check clue 1: Tesla is to the right of Arnold
        tesla_index = None
        for i, car in enumerate(car_p):
            if car == 'tesla model 3':
                tesla_index = i
                break
        if tesla_index <= arnold_index:
            continue
        
        # Build solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "CarModel", "Height"],
                "rows": [
                    ["1", name_p[0], mother_p[0], car_p[0], height_p[0]],
                    ["2", name_p[1], mother_p[1], car_p[1], height_p[1]]
                ]
            }
        }
        print(json.dumps(solution))
        return

solve_puzzle()