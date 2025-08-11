import itertools
import json

def main():
    names_left = ['Arnold', 'Alice', 'Eric']
    colors_left = ['yellow', 'red', 'white']
    
    for names_perm in itertools.permutations(names_left):
        names = ['Peter'] + list(names_perm)
        if not (names[2] == 'Arnold' and names[3] == 'Eric'):
            continue
        
        for colors_perm in itertools.permutations(colors_left):
            if colors_perm[2] != 'yellow':
                continue
            colors = [colors_perm[0], colors_perm[1], 'green', colors_perm[2]]
            
            try:
                red_index = colors.index('red')
                yellow_index = colors.index('yellow')
            except ValueError:
                continue
                
            if abs(red_index - yellow_index) == 2:
                rows = []
                for i in range(4):
                    rows.append([str(i+1), names[i], colors[i]])
                
                result = {
                    "solution": {
                        "header": ["House", "Name", "Color"],
                        "rows": rows
                    }
                }
                print(json.dumps(result))
                return
                
    error_result = {"error": "No solution found"}
    print(json.dumps(error_result))

if __name__ == "__main__":
    main()