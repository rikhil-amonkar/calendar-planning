import itertools
import json

# Generate permutations for each category
name_perms = list(itertools.permutations(['Arnold', 'Eric']))
hair_perms = list(itertools.permutations(['black', 'brown']))
sport_perms = list(itertools.permutations(['basketball', 'soccer']))
smoothie_perms = list(itertools.permutations(['desert', 'cherry']))

solution = None

for names in name_perms:
    for hairs in hair_perms:
        for sports in sport_perms:
            for smoothies in smoothie_perms:
                # Check constraint 1: Desert lover is Arnold
                desert_house = 0 if smoothies[0] == 'desert' else 1
                if names[desert_house] != 'Arnold':
                    continue
                
                # Check constraint 2: brown hair → basketball
                valid2 = True
                for i in [0, 1]:
                    if hairs[i] == 'brown' and sports[i] != 'basketball':
                        valid2 = False
                        break
                if not valid2:
                    continue
                
                # Check constraint 3: Arnold is left of black hair
                arnold_idx = names.index('Arnold')
                black_idx = hairs.index('black')
                if arnold_idx >= black_idx:
                    continue
                
                # All constraints satisfied
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                        "rows": []
                    }
                }
                # Build the rows
                for i in [0, 1]:
                    house_num = str(i + 1)
                    name = names[i]
                    hair = hairs[i]
                    sport = sports[i]
                    smoothie = smoothies[i]
                    solution["solution"]["rows"].append([
                        house_num, name, hair, sport, smoothie
                    ])
                # Exit all loops
                break
            if solution:
                break
        if solution:
            break
    if solution:
        break

# Output the JSON
print(json.dumps(solution, indent=2))