import itertools
import json

def main():
    # Fixed assignments from clues
    fixed_name_house4 = 'Alice'
    fixed_height_house2 = 'short'
    fixed_height_house5 = 'average'
    
    # Remaining names and heights to assign
    remaining_names = ['Peter', 'Bob', 'Eric', 'Arnold']
    remaining_heights = ['very tall', 'tall', 'very short']
    
    # Generate all permutations for names and heights
    for name_perm in itertools.permutations(remaining_names):
        for height_perm in itertools.permutations(remaining_heights):
            # Create assignment for all houses
            assignment = [
                {'house': 1, 'name': name_perm[0], 'height': height_perm[0]},
                {'house': 2, 'name': name_perm[1], 'height': fixed_height_house2},
                {'house': 3, 'name': name_perm[2], 'height': height_perm[1]},
                {'house': 4, 'name': fixed_name_house4, 'height': height_perm[2]},
                {'house': 5, 'name': name_perm[3], 'height': fixed_height_house5}
            ]
            
            # Check constraint 2: Peter directly left of Bob
            constraint2 = False
            for i in range(4):
                if assignment[i]['name'] == 'Peter' and assignment[i+1]['name'] == 'Bob':
                    constraint2 = True
                    break
            if not constraint2:
                continue
                
            # Check constraint 3: Eric left of Peter
            eric_house = None
            peter_house = None
            for h in assignment:
                if h['name'] == 'Eric':
                    eric_house = h['house']
                if h['name'] == 'Peter':
                    peter_house = h['house']
            if eric_house is None or peter_house is None or eric_house >= peter_house:
                continue
                
            # Check constraint 4: very tall directly left of Peter
            constraint4 = False
            for i in range(4):
                if assignment[i]['height'] == 'very tall' and assignment[i+1]['name'] == 'Peter':
                    constraint4 = True
                    break
            if not constraint4:
                continue
                
            # Check constraint 6: short and very short are adjacent
            very_short_house = None
            for h in assignment:
                if h['height'] == 'very short':
                    very_short_house = h['house']
                    break
            if very_short_house is None:
                continue
            if abs(very_short_house - 2) != 1:
                continue
                
            # All constraints satisfied, format the solution
            rows = []
            for house in assignment:
                rows.append([str(house['house']), house['name'], house['height']])
            
            result = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": rows
                }
            }
            
            print(json.dumps(result, indent=2))
            return
    
    print('No solution found')

if __name__ == '__main__':
    main()