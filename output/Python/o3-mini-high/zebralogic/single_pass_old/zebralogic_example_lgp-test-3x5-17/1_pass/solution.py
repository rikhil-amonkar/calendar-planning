#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Eric", "Arnold", "Peter"]
    phones = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
    heights = ["very short", "average", "short"]
    styles = ["colonial", "ranch", "victorian"]
    cars = ["tesla model 3", "toyota camry", "ford f150"]

    solutions = []
    
    for name_perm in itertools.permutations(names):
        # Clue 7: Arnold is in the second house.
        if name_perm[1] != "Arnold":
            continue
        # Clue 1: Peter is somewhere to the right of Eric.
        if name_perm.index("Peter") <= name_perm.index("Eric"):
            continue

        for phone_perm in itertools.permutations(phones):
            # Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
            try:
                iphone_index = phone_perm.index("iphone 13")
            except ValueError:
                continue
            if iphone_index == 2:
                continue
            if phone_perm[iphone_index + 1] != "google pixel 6":
                continue

            for height_perm in itertools.permutations(heights):
                # Clue 9: The person who has an average height is in the first house.
                if height_perm[0] != "average":
                    continue
                # Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
                short_index = height_perm.index("short")
                if short_index == 2:
                    continue
                if phone_perm[short_index + 1] != "samsung galaxy s21":
                    continue

                for style_perm in itertools.permutations(styles):
                    # Clue 2: The person living in a colonial-style house is in the second house.
                    if style_perm[1] != "colonial":
                        continue
                    # Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
                    if style_perm.index("colonial") <= style_perm.index("ranch"):
                        continue

                    for car_perm in itertools.permutations(cars):
                        # Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
                        if car_perm.index("ford f150") <= car_perm.index("toyota camry"):
                            continue
                        # Clue 3: The person who owns a Tesla Model 3 is the person who is very short.
                        if car_perm.index("tesla model 3") != height_perm.index("very short"):
                            continue
                        
                        # If we reach here, all conditions have been met.
                        current_solution = []
                        for i in range(3):
                            current_solution.append([
                                str(i+1),
                                name_perm[i],
                                phone_perm[i],
                                height_perm[i],
                                style_perm[i],
                                car_perm[i]
                            ])
                        solutions.append(current_solution)
    
    if solutions:
        # Assuming unique solution, take the first one
        output = {
            "solution": {
                "header": ["House", "Name", "phone", "height", "style", "car"],
                "rows": solutions[0]
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": {"header": ["House", "Name", "phone", "height", "style", "car"], "rows": []}}))

if __name__ == "__main__":
    main()