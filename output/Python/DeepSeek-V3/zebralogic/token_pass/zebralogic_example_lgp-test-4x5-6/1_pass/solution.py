import json
from itertools import permutations

def solve():
    # Define all possible values
    names = ["Peter", "Eric", "Alice", "Arnold"]
    educations = ["bachelor", "high school", "associate", "master"]
    musics = ["jazz", "rock", "pop", "classical"]
    colors = ["green", "red", "yellow", "white"]
    flowers = ["lilies", "carnations", "daffodils", "roses"]
    
    houses = [1, 2, 3, 4]
    
    # Generate all permutations for each category
    name_perms = list(permutations(names, 4))
    edu_perms = list(permutations(educations, 4))
    music_perms = list(permutations(musics, 4))
    color_perms = list(permutations(colors, 4))
    flower_perms = list(permutations(flowers, 4))
    
    solutions = []
    
    # Brute force search through all combinations
    for name_assignment in name_perms:
        # Check clue 5: Eric is not in the second house
        if name_assignment[1] == "Eric":
            continue
        # Check clue 6: Arnold is not in the third house
        if name_assignment[2] == "Arnold":
            continue
        
        for edu_assignment in edu_perms:
            # Check clue 3: The person with a master's degree is Alice
            # Find Alice's house index
            alice_house = name_assignment.index("Alice")
            if edu_assignment[alice_house] != "master":
                continue
            
            # Check clue 9: The person with an associate's degree is not in the fourth house
            if edu_assignment[3] == "associate":
                continue
            
            for music_assignment in music_perms:
                # Check clue 8: The person who loves pop music is in the second house
                if music_assignment[1] != "pop":
                    continue
                
                # Check clue 4: The person with a master's degree is directly left of the person who loves classical music
                # Alice (master) must be directly left of classical
                classical_house = music_assignment.index("classical")
                if classical_house != alice_house + 1:
                    continue
                
                # Check clue 12: The person whose favorite color is red is the person who loves rock music
                # We'll check this with color assignments
                
                for color_assignment in color_perms:
                    # Check clue 13: Arnold is the person who loves yellow
                    arnold_house = name_assignment.index("Arnold")
                    if color_assignment[arnold_house] != "yellow":
                        continue
                    
                    # Check clue 11: The person whose favorite color is red is directly left of the person who loves white
                    red_house = color_assignment.index("red")
                    white_house = color_assignment.index("white")
                    if white_house != red_house + 1:
                        continue
                    
                    # Check clue 12: The person whose favorite color is red is the person who loves rock music
                    if music_assignment[red_house] != "rock":
                        continue
                    
                    # Check clue 7: The person who loves yellow is directly left of the person who loves the rose bouquet
                    # We'll check this with flower assignments
                    
                    for flower_assignment in flower_perms:
                        # Check clue 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils
                        bachelor_house = edu_assignment.index("bachelor")
                        if flower_assignment[bachelor_house] != "daffodils":
                            continue
                        
                        # Check clue 2: The person who loves a carnations arrangement is not in the first house
                        if flower_assignment[0] == "carnations":
                            continue
                        
                        # Check clue 10: The person who loves a carnations arrangement is not in the fourth house
                        if flower_assignment[3] == "carnations":
                            continue
                        
                        # Check clue 14: The person who loves a bouquet of daffodils is the person who loves yellow
                        daffodils_house = flower_assignment.index("daffodils")
                        if color_assignment[daffodils_house] != "yellow":
                            continue
                        
                        # Check clue 7: The person who loves yellow is directly left of the person who loves the rose bouquet
                        yellow_house = color_assignment.index("yellow")
                        roses_house = flower_assignment.index("roses")
                        if roses_house != yellow_house + 1:
                            continue
                        
                        # All constraints satisfied - found a solution
                        solution = []
                        for i in range(4):
                            solution.append([
                                str(i + 1),
                                name_assignment[i],
                                edu_assignment[i],
                                music_assignment[i],
                                color_assignment[i],
                                flower_assignment[i]
                            ])
                        solutions.append(solution)
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"], "rows": []}}
    
    # Take the first solution (should be unique)
    result = {
        "solution": {
            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
            "rows": solutions[0]
        }
    }
    return result

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, indent=2))