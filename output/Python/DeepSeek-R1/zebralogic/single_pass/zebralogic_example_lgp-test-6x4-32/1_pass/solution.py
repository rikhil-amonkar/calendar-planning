import itertools
import json

def main():
    names_list = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
    styles_list = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
    musics_list = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
    hobbies_list = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']
    
    solution_found = None
    
    for carol_house in [1, 3]:
        for jazz_house in [2, 3]:
            if carol_house == jazz_house:
                continue
            if jazz_house == 2:
                eric_house = 3
            else:
                eric_house = 4
            if carol_house == eric_house:
                continue
                
            names = [None] * 6
            styles = [None] * 6
            musics = [None] * 6
            hobbies = [None] * 6
            
            musics[0] = 'country'
            musics[4] = 'rock'
            names[2] = 'Bob'
            
            names[carol_house] = 'Carol'
            musics[carol_house] = 'hip hop'
            styles[carol_house] = 'mediterranean'
            
            musics[jazz_house] = 'jazz'
            names[eric_house] = 'Eric'
            styles[eric_house] = 'ranch'
            hobbies[eric_house] = 'gardening'
            
            unassigned_name_houses = [i for i in range(6) if names[i] is None]
            unassigned_names = [n for n in names_list if n not in ['Carol', 'Eric', 'Bob']]
            
            unassigned_style_houses = [i for i in range(6) if styles[i] is None]
            unassigned_styles = [s for s in styles_list if s not in ['mediterranean', 'ranch']]
            
            unassigned_music_houses = [i for i in range(6) if musics[i] is None]
            unassigned_musics = [m for m in musics_list if m not in ['country', 'hip hop', 'jazz', 'rock']]
            
            unassigned_hobby_houses = [i for i in range(6) if hobbies[i] is None]
            unassigned_hobbies = [h for h in hobbies_list if h != 'gardening']
            
            for name_perm in itertools.permutations(unassigned_names):
                names_current = names[:]
                for idx, house in enumerate(unassigned_name_houses):
                    names_current[house] = name_perm[idx]
                    
                for style_perm in itertools.permutations(unassigned_styles):
                    styles_current = styles[:]
                    for idx, house in enumerate(unassigned_style_houses):
                        styles_current[house] = style_perm[idx]
                        
                    for music_perm in itertools.permutations(unassigned_musics):
                        musics_current = musics[:]
                        for idx, house in enumerate(unassigned_music_houses):
                            musics_current[house] = music_perm[idx]
                            
                        for hobby_perm in itertools.permutations(unassigned_hobbies):
                            hobbies_current = hobbies[:]
                            for idx, house in enumerate(unassigned_hobby_houses):
                                hobbies_current[house] = hobby_perm[idx]
                            
                            arnold_index = names_current.index('Arnold')
                            if styles_current[arnold_index] != 'craftsman':
                                continue
                            
                            alice_index = names_current.index('Alice')
                            if hobbies_current[alice_index] != 'photography':
                                continue
                            
                            woodworking_index = None
                            for i in range(6):
                                if hobbies_current[i] == 'woodworking':
                                    woodworking_index = i
                                    if styles_current[i] != 'victorian':
                                        break
                            else:
                                if woodworking_index is None:
                                    continue
                                if styles_current[woodworking_index] != 'victorian':
                                    continue
                            
                            victorian_index = styles_current.index('victorian')
                            if hobbies_current[victorian_index] != 'woodworking':
                                continue
                            
                            classical_index = musics_current.index('classical')
                            if abs(classical_index - woodworking_index) != 1:
                                continue
                            
                            if abs(arnold_index - victorian_index) != 3:
                                continue
                            
                            knitting_index = hobbies_current.index('knitting')
                            if carol_house >= knitting_index:
                                continue
                            
                            painting_index = hobbies_current.index('painting')
                            colonial_index = styles_current.index('colonial')
                            if abs(painting_index - colonial_index) != 2:
                                continue
                            
                            solution_rows = []
                            for i in range(6):
                                solution_rows.append([str(i+1), names_current[i], styles_current[i], musics_current[i], hobbies_current[i]])
                            
                            solution_found = solution_rows
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
            break
            
    if solution_found is None:
        print('No solution found')
        return

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
            "rows": solution_found
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()