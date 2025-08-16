import itertools
import json

def main():
    names_list = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    mothers_list = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
    heights_list = ['average', 'very short', 'short', 'very tall', 'tall']
    
    for names in itertools.permutations(names_list):
        try:
            idx_bob = names.index('Bob')
            idx_alice = names.index('Alice')
            idx_eric = names.index('Eric')
        except ValueError:
            continue
            
        if names[1] == 'Peter':
            continue
        if names[4] == 'Eric':
            continue
            
        for mothers in itertools.permutations(mothers_list):
            try:
                idx_penny = mothers.index('Penny')
                idx_holly = mothers.index('Holly')
            except ValueError:
                continue
                
            if mothers[idx_bob] != 'Janelle':
                continue
            if mothers[idx_alice] != 'Aniya':
                continue
            if mothers[idx_eric] != 'Kailyn':
                continue
                
            for heights in itertools.permutations(heights_list):
                if heights[4] != 'very short':
                    continue
                    
                try:
                    idx_avg = heights.index('average')
                    idx_short = heights.index('short')
                    idx_very_tall = heights.index('very tall')
                except ValueError:
                    continue
                    
                if idx_avg >= idx_penny:
                    continue
                    
                if idx_short == 4:
                    continue
                if names[idx_short+1] != 'Arnold':
                    continue
                    
                if names[idx_very_tall] != 'Arnold':
                    continue
                    
                if idx_bob == 4:
                    continue
                if heights[idx_bob+1] != 'average':
                    continue
                    
                if idx_very_tall <= idx_holly:
                    continue
                    
                rows = []
                for i in range(5):
                    rows.append([str(i+1), names[i], mothers[i], heights[i]])
                    
                solution_dict = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Height"],
                        "rows": rows
                    }
                }
                print(json.dumps(solution_dict))
                return
                
    print(json.dumps({"solution": {"header": ["House", "Name", "Mother", "Height"], "rows": []}}))

if __name__ == '__main__':
    main()