import itertools
import json

def main():
    names_all = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
    styles_all = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
    music_all = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
    hobbies_all = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']
    
    solution_found = False
    result_solution = None
    
    for names in itertools.permutations(names_all):
        if names[2] != 'Bob':
            continue
        try:
            carol_index = names.index('Carol')
            eric_index = names.index('Eric')
            arnold_index = names.index('Arnold')
            alice_index = names.index('Alice')
        except ValueError:
            continue
            
        if eric_index == 0:
            continue
            
        for styles in itertools.permutations(styles_all):
            if styles[carol_index] != 'mediterranean':
                continue
            if styles[eric_index] != 'ranch':
                continue
            if styles[arnold_index] != 'craftsman':
                continue
                
            for music in itertools.permutations(music_all):
                if music[0] != 'country':
                    continue
                if music[4] != 'rock':
                    continue
                if music[carol_index] != 'hip hop':
                    continue
                if music[eric_index - 1] != 'jazz':
                    continue
                    
                for hobby in itertools.permutations(hobbies_all):
                    if hobby[eric_index] != 'gardening':
                        continue
                    if hobby[alice_index] != 'photography':
                        continue
                    try:
                        victorian_index = styles.index('victorian')
                    except ValueError:
                        continue
                    if hobby[victorian_index] != 'woodworking':
                        continue
                    
                    try:
                        classical_index = music.index('classical')
                    except ValueError:
                        continue
                    if abs(classical_index - victorian_index) != 1:
                        continue
                    
                    try:
                        knitting_index = hobby.index('knitting')
                    except ValueError:
                        continue
                    if carol_index >= knitting_index:
                        continue
                    
                    if abs(arnold_index - victorian_index) != 3:
                        continue
                    
                    try:
                        painting_index = hobby.index('painting')
                        colonial_index = styles.index('colonial')
                    except ValueError:
                        continue
                    if abs(painting_index - colonial_index) != 2:
                        continue
                    
                    solution_found = True
                    header = ["House", "Name", "House Style", "Favorite Music Genre", "Hobby"]
                    rows = []
                    for i in range(6):
                        row = [str(i+1), names[i], styles[i], music[i], hobby[i]]
                        rows.append(row)
                    result_solution = {
                        "solution": {
                            "header": header,
                            "rows": rows
                        }
                    }
                    break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
            
    if not solution_found:
        result_solution = {"solution": {}}
        
    print(json.dumps(result_solution))

if __name__ == "__main__":
    main()