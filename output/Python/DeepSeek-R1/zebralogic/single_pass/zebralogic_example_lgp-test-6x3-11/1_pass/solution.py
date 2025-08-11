import itertools
import json

def main():
    names_list = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
    hairs_list = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
    heights_list = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']
    
    found = False
    solution_rows = None
    
    for names in itertools.permutations(names_list):
        if names[3] != 'Alice':
            continue
        
        for hairs in itertools.permutations(hairs_list):
            if hairs[2] != 'gray':
                continue
            if hairs[3] == 'black':
                continue
            
            for heights in itertools.permutations(heights_list):
                if heights[4] != 'very short':
                    continue
                if heights[5] != 'tall':
                    continue
                
                if 'blonde' in hairs:
                    i_blonde = hairs.index('blonde')
                    if i_blonde >= 5 or names[i_blonde+1] != 'Bob':
                        continue
                else:
                    continue
                
                if 'short' in heights:
                    i_short = heights.index('short')
                    if names[i_short] != 'Arnold':
                        continue
                else:
                    continue
                
                if 'red' in hairs:
                    i_red = hairs.index('red')
                    if names[i_red] != 'Eric':
                        continue
                else:
                    continue
                
                if 'average' in heights and 'super tall' in heights:
                    i_avg = heights.index('average')
                    i_sup = heights.index('super tall')
                    if i_sup <= i_avg:
                        continue
                else:
                    continue
                
                if names[i_blonde] != 'Carol':
                    continue
                
                i_gray = hairs.index('gray')
                if abs(i_gray - i_red) != 2:
                    continue
                
                if 'Bob' in names:
                    i_bob = names.index('Bob')
                    if hairs[i_bob] != 'brown':
                        continue
                else:
                    continue
                
                if heights[i_blonde] != 'very tall':
                    continue
                
                found = True
                solution_rows = []
                for i in range(6):
                    solution_rows.append([str(i+1), names[i], hairs[i], heights[i]])
                break
            if found:
                break
        if found:
            break
    
    if found:
        result = {
            "solution": {
                "header": ["House", "name", "hair", "height"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result))
    else:
        result = {
            "solution": {
                "header": ["House", "name", "hair", "height"],
                "rows": []
            }
        }
        print(json.dumps(result))

if __name__ == '__main__':
    main()