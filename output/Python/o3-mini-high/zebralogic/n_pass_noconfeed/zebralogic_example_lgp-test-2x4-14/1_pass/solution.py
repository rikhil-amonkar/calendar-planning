import json
import itertools

def solve_puzzle():
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    smoothies = ["cherry", "desert"]
    pets = ["dog", "cat"]

    solutions = []
    # Iterate over all possible assignments of attributes across the 2 houses.
    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(house_styles):
            for smoothie_perm in itertools.permutations(smoothies):
                for pet_perm in itertools.permutations(pets):
                    valid = True
                    
                    # Clue 1: The person who likes Cherry smoothies is the person who owns a dog.
                    for i in range(2):
                        if smoothie_perm[i] == "cherry" and pet_perm[i] != "dog":
                            valid = False
                            break
                        if pet_perm[i] == "dog" and smoothie_perm[i] != "cherry":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 2: The person residing in a Victorian house is the person who owns a dog.
                    for i in range(2):
                        if style_perm[i] == "victorian" and pet_perm[i] != "dog":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 3: The person residing in a Victorian house is somewhere to the left of Eric.
                    victorian_index = None
                    eric_index = None
                    for i in range(2):
                        if style_perm[i] == "victorian":
                            victorian_index = i
                        if name_perm[i] == "Eric":
                            eric_index = i
                    if victorian_index is None or eric_index is None or victorian_index >= eric_index:
                        valid = False
                    if not valid:
                        continue

                    solutions.append((name_perm, style_perm, smoothie_perm, pet_perm))
    
    return solutions

def main():
    solutions = solve_puzzle()
    if solutions:
        # Select the first valid solution
        name_perm, style_perm, smoothie_perm, pet_perm = solutions[0]
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
                "rows": []
            }
        }
        # Houses are numbered from 1 to 2.
        for i in range(2):
            result["solution"]["rows"].append([
                str(i+1),
                name_perm[i],
                style_perm[i],
                smoothie_perm[i],
                pet_perm[i]
            ])
        print(json.dumps(result))

if __name__ == "__main__":
    main()