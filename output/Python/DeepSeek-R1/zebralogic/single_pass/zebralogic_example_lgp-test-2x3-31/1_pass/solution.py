import json

def main():
    names = ['Eric', 'Arnold']
    sports = ['basketball', 'soccer']
    hobbies = ['photography', 'gardening']
    
    name_perms = [(names[0], names[1]), (names[1], names[0])]
    sport_perms = [(sports[0], sports[1]), (sports[1], sports[0])]
    hobby_perms = [(hobbies[0], hobbies[1]), (hobbies[1], hobbies[0])]
    
    found = False
    solution_candidate = None
    
    for name_perm in name_perms:
        for sport_perm in sport_perms:
            for hobby_perm in hobby_perms:
                house1 = [1, name_perm[0], sport_perm[0], hobby_perm[0]]
                house2 = [2, name_perm[1], sport_perm[1], hobby_perm[1]]
                candidate = [house1, house2]
                
                valid = True
                for house in candidate:
                    if house[1] == 'Arnold':
                        if house[3] != 'gardening':
                            valid = False
                            break
                    if house[3] == 'gardening':
                        if house[1] != 'Arnold':
                            valid = False
                            break
                if not valid:
                    continue
                    
                if candidate[0][3] == 'photography':
                    valid = False
                if not valid:
                    continue
                    
                if candidate[0][2] == 'soccer':
                    valid = False
                if not valid:
                    continue
                    
                solution_candidate = candidate
                found = True
                break
            if found:
                break
        if found:
            break
            
    if solution_candidate:
        rows = []
        for house in solution_candidate:
            row = [str(house[0]), house[1], house[2], house[3]]
            rows.append(row)
        result = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "Hobby"],
                "rows": rows
            }
        }
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "Hobby"],
                "rows": []
            }
        }
        
    print(json.dumps(result))

if __name__ == "__main__":
    main()