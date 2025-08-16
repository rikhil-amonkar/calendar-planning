import itertools
import json

def main():
    names = ['Eric', 'Arnold', 'Peter']
    heights = ['very short', 'short', 'average']
    
    solution_rows = None
    
    for name_perm in itertools.permutations(names):
        if name_perm[0] != 'Peter':
            continue
            
        for height_perm in itertools.permutations(heights):
            eric_index = name_perm.index('Eric')
            if height_perm[eric_index] != 'very short':
                continue
                
            short_index = height_perm.index('short')
            if eric_index < short_index:
                solution_rows = []
                for i in range(3):
                    house_num = str(i + 1)
                    solution_rows.append([house_num, name_perm[i], height_perm[i]])
                break
        if solution_rows is not None:
            break
            
    if solution_rows is None:
        solution_rows = []
        
    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": solution_rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()