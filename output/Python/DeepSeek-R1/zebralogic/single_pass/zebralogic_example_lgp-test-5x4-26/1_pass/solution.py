import itertools
import json

def main():
    # Fixed values from clues
    fixed_house5_name = 'Bob'
    fixed_house3_mother = 'Kailyn'
    fixed_house1_height = 'average'
    fixed_house4_height = 'short'
    
    # Remaining values for permutation
    remaining_names = ['Alice', 'Peter', 'Eric', 'Arnold']
    remaining_heights = ['very short', 'tall', 'very tall']
    remaining_mothers = ['Janelle', 'Penny', 'Holly', 'Aniya']
    
    solution_found = None
    
    for n_perm in itertools.permutations(remaining_names):
        names = list(n_perm)
        names.append(fixed_house5_name)
        
        try:
            eric_index = names.index('Eric')
            peter_index = names.index('Peter')
            arnold_index = names.index('Arnold')
            alice_index = names.index('Alice')
        except ValueError:
            continue
        
        for h_perm in itertools.permutations(remaining_heights):
            heights = [
                fixed_house1_height,
                h_perm[0],
                h_perm[1],
                fixed_house4_height,
                h_perm[2]
            ]
            
            very_short_index = None
            tall_index = None
            for idx, h in enumerate(heights):
                if h == 'very short':
                    very_short_index = idx
                elif h == 'tall':
                    tall_index = idx
            
            if very_short_index is None or tall_index is None:
                continue
                
            for m_perm in itertools.permutations(remaining_mothers):
                mothers = [
                    m_perm[0],
                    m_perm[1],
                    fixed_house3_mother,
                    m_perm[2],
                    m_perm[3]
                ]
                
                if mothers[very_short_index] != 'Penny':
                    continue
                if mothers[tall_index] != 'Holly':
                    continue
                
                for ha0 in ['blonde', 'gray']:
                    for ha1 in ['blonde', 'gray']:
                        if ha0 == ha1:
                            continue
                        hairs = [None] * 5
                        hairs[eric_index] = 'black'
                        hairs[peter_index] = 'red'
                        hairs[arnold_index] = 'brown'
                        hairs[alice_index] = ha0
                        hairs[4] = ha1
                        
                        if hairs[3] == 'black':
                            continue
                        
                        gray_index = None
                        for i in range(5):
                            if hairs[i] == 'gray':
                                gray_index = i
                                break
                        if gray_index is None or gray_index >= 4:
                            continue
                        if mothers[gray_index + 1] != 'Janelle':
                            continue
                        
                        if abs(eric_index - gray_index) != 1:
                            continue
                            
                        if arnold_index >= (gray_index + 1):
                            continue
                            
                        aniya_index = None
                        for i in range(5):
                            if mothers[i] == 'Aniya':
                                aniya_index = i
                                break
                        if aniya_index is None:
                            continue
                        if abs(aniya_index - very_short_index) != 1:
                            continue
                            
                        solution_rows = []
                        for i in range(5):
                            solution_rows.append([str(i+1), names[i], heights[i], mothers[i], hairs[i]])
                        
                        solution_found = {
                            "header": ["House", "Name", "Height", "Mother", "HairColor"],
                            "rows": solution_rows
                        }
                        break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    
    if solution_found:
        result = {
            "solution": solution_found
        }
        print(json.dumps(result))
    else:
        print('{"solution": {}}')

if __name__ == '__main__':
    main()