import itertools
import json

def main():
    fixed_flowers = ['carnations', 'daffodils', 'lilies']  # for house0, house1, house2
    names_list = ['Arnold', 'Eric', 'Peter']
    hair_remaining = ['black', 'brown']   # for house0 and house2
    sport_remaining = ['basketball', 'tennis']  # for house0 and house1
    style_remaining = ['ranch', 'victorian']    # for house0 and house1
    pet_remaining = ['fish', 'dog']             # for house0 and house1

    solutions = []
    for names in itertools.permutations(names_list):
        for hair0, hair2 in itertools.permutations(hair_remaining):
            hair = [hair0, 'blonde', hair2]
            for sport0, sport1 in itertools.permutations(sport_remaining):
                sports = [sport0, sport1, 'soccer']
                for style0, style1 in itertools.permutations(style_remaining):
                    styles = [style0, style1, 'colonial']
                    for pet0, pet1 in itertools.permutations(pet_remaining):
                        pets = [pet0, pet1, 'cat']
                        house0 = (names[0], fixed_flowers[0], hair[0], sports[0], styles[0], pets[0])
                        house1 = (names[1], fixed_flowers[1], hair[1], sports[1], styles[1], pets[1])
                        house2 = (names[2], fixed_flowers[2], hair[2], sports[2], styles[2], pets[2])
                        houses = [house0, house1, house2]
                        
                        # Constraint 4: Peter loves basketball.
                        peter_index = None
                        for idx, name in enumerate(names):
                            if name == 'Peter':
                                peter_index = idx
                                break
                        if peter_index is None:
                            continue
                        if sports[peter_index] != 'basketball':
                            continue
                            
                        # Constraint 5: Arnold is directly left of ranch.
                        arnold_index = None
                        for idx, name in enumerate(names):
                            if name == 'Arnold':
                                arnold_index = idx
                                break
                        if arnold_index is None:
                            continue
                        if arnold_index == 2:
                            continue
                        if styles[arnold_index+1] != 'ranch':
                            continue
                            
                        # Constraint 6: Dog owner loves basketball.
                        valid6 = True
                        for i in range(3):
                            if pets[i] == 'dog':
                                if sports[i] != 'basketball':
                                    valid6 = False
                                    break
                        if not valid6:
                            continue
                            
                        # Constraint 9: Arnold is left of black hair.
                        black_index = None
                        for idx, color in enumerate(hair):
                            if color == 'black':
                                black_index = idx
                                break
                        if black_index is None:
                            continue
                        if arnold_index >= black_index:
                            continue
                            
                        solutions.append(houses)
    
    if solutions:
        sol = solutions[0]
        header = ["House", "Name", "Favorite Flower", "Hair Colors", "Favorite Sports", "House Style", "Pet"]
        rows = []
        for i, house in enumerate(sol):
            row = [str(i+1)]
            row.extend(house)
            rows.append(row)
        
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == "__main__":
    main()