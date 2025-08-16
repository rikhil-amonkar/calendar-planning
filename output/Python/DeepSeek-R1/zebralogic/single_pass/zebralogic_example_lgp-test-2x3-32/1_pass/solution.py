import itertools
import json

def main():
    names = ['Eric', 'Arnold']
    birthdays = ['april', 'sept']
    colors = ['yellow', 'red']
    
    for name_perm in itertools.permutations(names):
        for bday_perm in itertools.permutations(birthdays):
            for color_perm in itertools.permutations(colors):
                house1 = (name_perm[0], bday_perm[0], color_perm[0])
                house2 = (name_perm[1], bday_perm[1], color_perm[1])
                
                if house1[1] != 'april':
                    continue
                if house1[2] == 'yellow':
                    continue
                if house2[0] != 'Eric' or house2[2] != 'yellow':
                    continue
                
                sol_dict = {
                    "solution": {
                        "header": ["House", "Name", "Birthday", "Color"],
                        "rows": [
                            ["1", house1[0], house1[1], house1[2]],
                            ["2", house2[0], house2[1], house2[2]]
                        ]
                    }
                }
                print(json.dumps(sol_dict))
                return
                
    sol_dict = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": []
        }
    }
    print(json.dumps(sol_dict))

if __name__ == '__main__':
    main()