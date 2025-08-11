import itertools
import json

def main():
    names = ['Eric', 'Arnold']
    styles = ['victorian', 'colonial']
    solutions = []
    
    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(styles):
            candidate = {
                1: {'Name': name_perm[0], 'House Style': style_perm[0]},
                2: {'Name': name_perm[1], 'House Style': style_perm[1]}
            }
            
            if candidate[1]['Name'] != 'Eric':
                continue
                
            v_house = None
            c_house = None
            for house_num in [1, 2]:
                style_val = candidate[house_num]['House Style']
                if style_val == 'victorian':
                    v_house = house_num
                elif style_val == 'colonial':
                    c_house = house_num
                    
            if v_house is not None and c_house is not None and v_house < c_house:
                rows = [
                    ['1', candidate[1]['Name'], candidate[1]['House Style']],
                    ['2', candidate[2]['Name'], candidate[2]['House Style']]
                ]
                sol = {
                    "header": ["House", "Name", "House Style"],
                    "rows": rows
                }
                solutions.append(sol)
    
    output = {"solution": solutions[0]} if solutions else {"solution": {}}
    print(json.dumps(output))

if __name__ == "__main__":
    main()