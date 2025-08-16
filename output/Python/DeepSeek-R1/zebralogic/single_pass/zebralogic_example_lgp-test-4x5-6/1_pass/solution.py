import itertools
import json

def main():
    names = ['Peter', 'Eric', 'Alice', 'Arnold']
    educations = ['bachelor', 'high school', 'associate', 'master']
    musics = ['jazz', 'rock', 'pop', 'classical']
    colors = ['green', 'red', 'yellow', 'white']
    flowers = ['lilies', 'carnations', 'daffodils', 'roses']
    
    def check_constraints(assn):
        if assn[1]['MusicGenre'] != 'pop':
            return False
            
        if assn[0]['Flower'] == 'carnations':
            return False
            
        if assn[1]['Name'] == 'Eric':
            return False
            
        if assn[2]['Name'] == 'Arnold':
            return False
            
        if assn[3]['Education'] == 'associate':
            return False
            
        if assn[3]['Flower'] == 'carnations':
            return False
            
        for i in range(4):
            if assn[i]['Education'] == 'bachelor' and assn[i]['Flower'] != 'daffodils':
                return False
            if assn[i]['Flower'] == 'daffodils' and assn[i]['Education'] != 'bachelor':
                return False
                
        found_clue3 = False
        for i in range(4):
            if assn[i]['Education'] == 'master' and assn[i]['Name'] == 'Alice':
                found_clue3 = True
                break
        if not found_clue3:
            return False
            
        found_clue4 = False
        for i in range(3):
            if assn[i]['Education'] == 'master' and assn[i+1]['MusicGenre'] == 'classical':
                found_clue4 = True
                break
        if not found_clue4:
            return False
            
        found_clue7 = False
        for i in range(3):
            if assn[i]['Color'] == 'yellow' and assn[i+1]['Flower'] == 'roses':
                found_clue7 = True
                break
        if not found_clue7:
            return False
            
        found_clue11 = False
        for i in range(3):
            if assn[i]['Color'] == 'red' and assn[i+1]['Color'] == 'white':
                found_clue11 = True
                break
        if not found_clue11:
            return False
            
        found_clue12 = False
        for i in range(4):
            if assn[i]['Color'] == 'red' and assn[i]['MusicGenre'] == 'rock':
                found_clue12 = True
                break
        if not found_clue12:
            return False
            
        found_clue13 = False
        for i in range(4):
            if assn[i]['Name'] == 'Arnold' and assn[i]['Color'] == 'yellow':
                found_clue13 = True
                break
        if not found_clue13:
            return False
            
        found_clue14 = False
        for i in range(4):
            if assn[i]['Flower'] == 'daffodils' and assn[i]['Color'] == 'yellow':
                found_clue14 = True
                break
        if not found_clue14:
            return False
            
        return True

    found_solution = False
    result_json = None

    for name_perm in itertools.permutations(names):
        if found_solution:
            break
        for edu_perm in itertools.permutations(educations):
            if found_solution:
                break
            for music_perm in itertools.permutations(musics):
                if found_solution:
                    break
                for color_perm in itertools.permutations(colors):
                    if found_solution:
                        break
                    for flower_perm in itertools.permutations(flowers):
                        assignment = []
                        for i in range(4):
                            house = {
                                'Name': name_perm[i],
                                'Education': edu_perm[i],
                                'MusicGenre': music_perm[i],
                                'Color': color_perm[i],
                                'Flower': flower_perm[i]
                            }
                            assignment.append(house)
                        
                        if check_constraints(assignment):
                            rows = []
                            for idx, house_dict in enumerate(assignment, start=1):
                                row = [str(idx), house_dict['Name'], house_dict['Education'], house_dict['MusicGenre'], house_dict['Color'], house_dict['Flower']]
                                rows.append(row)
                            
                            solution_dict = {
                                "solution": {
                                    "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                                    "rows": rows
                                }
                            }
                            result_json = json.dumps(solution_dict, indent=2)
                            found_solution = True
                            break
    
    if found_solution:
        print(result_json)
    else:
        print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == '__main__':
    main()