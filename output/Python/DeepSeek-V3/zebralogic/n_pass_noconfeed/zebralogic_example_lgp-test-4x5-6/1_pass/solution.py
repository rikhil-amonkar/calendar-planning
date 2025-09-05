import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Peter', 'Eric', 'Alice', 'Arnold']
    educations = ['bachelor', 'high school', 'associate', 'master']
    music_genres = ['jazz', 'rock', 'pop', 'classical']
    colors = ['green', 'red', 'yellow', 'white']
    flowers = ['lilies', 'carnations', 'daffodils', 'roses']
    
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each category
    name_perms = list(permutations(names))
    education_perms = list(permutations(educations))
    music_perms = list(permutations(music_genres))
    color_perms = list(permutations(colors))
    flower_perms = list(permutations(flowers))
    
    # Try all combinations until we find one that satisfies all constraints
    for name_assignment in name_perms:
        # Check clue 5: Eric is not in the second house
        if name_assignment[1] == 'Eric':
            continue
            
        # Check clue 6: Arnold is not in the third house
        if name_assignment[2] == 'Arnold':
            continue
            
        for education_assignment in education_perms:
            # Check clue 3: The person with a master's degree is Alice
            master_index = education_assignment.index('master')
            if name_assignment[master_index] != 'Alice':
                continue
                
            # Check clue 9: The person with an associate's degree is not in the fourth house
            if education_assignment[3] == 'associate':
                continue
                
            for music_assignment in music_perms:
                # Check clue 8: The person who loves pop music is in the second house
                if music_assignment[1] != 'pop':
                    continue
                    
                # Check clue 4: The person with a master's degree is directly left of the person who loves classical music
                master_house = education_assignment.index('master') + 1
                classical_house = music_assignment.index('classical') + 1
                if classical_house != master_house + 1:
                    continue
                    
                for color_assignment in color_perms:
                    # Check clue 13: Arnold is the person who loves yellow
                    arnold_index = name_assignment.index('Arnold')
                    if color_assignment[arnold_index] != 'yellow':
                        continue
                        
                    # Check clue 11: The person whose favorite color is red is directly left of the person who loves white
                    red_index = color_assignment.index('red')
                    white_index = color_assignment.index('white')
                    if white_index != red_index + 1:
                        continue
                        
                    # Check clue 12: The person whose favorite color is red is the person who loves rock music
                    if music_assignment[red_index] != 'rock':
                        continue
                        
                    for flower_assignment in flower_perms:
                        # Check clue 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils
                        bachelor_index = education_assignment.index('bachelor')
                        if flower_assignment[bachelor_index] != 'daffodils':
                            continue
                            
                        # Check clue 2: The person who loves a carnations arrangement is not in the first house
                        if flower_assignment[0] == 'carnations':
                            continue
                            
                        # Check clue 10: The person who loves a carnations arrangement is not in the fourth house
                        if flower_assignment[3] == 'carnations':
                            continue
                            
                        # Check clue 7: The person who loves yellow is directly left of the person who loves the rose bouquet
                        yellow_index = color_assignment.index('yellow')
                        rose_index = flower_assignment.index('roses')
                        if rose_index != yellow_index + 1:
                            continue
                            
                        # Check clue 14: The person who loves a bouquet of daffodils is the person who loves yellow
                        daffodils_index = flower_assignment.index('daffodils')
                        if color_assignment[daffodils_index] != 'yellow':
                            continue
                            
                        # All constraints satisfied, build the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                                "rows": []
                            }
                        }
                        
                        for i in range(4):
                            row = [
                                str(i + 1),
                                name_assignment[i],
                                education_assignment[i],
                                music_assignment[i],
                                color_assignment[i],
                                flower_assignment[i]
                            ]
                            solution["solution"]["rows"].append(row)
                        
                        # Output the solution as JSON
                        print(json.dumps(solution, indent=2))
                        return
    
    print('{"solution": {"header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"], "rows": []}}')

if __name__ == "__main__":
    main()