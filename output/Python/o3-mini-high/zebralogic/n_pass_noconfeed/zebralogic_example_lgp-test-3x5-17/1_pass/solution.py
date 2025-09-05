import itertools
import json

def main():
    names = ["Eric", "Arnold", "Peter"]
    phones = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
    heights = ["very short", "average", "short"]
    house_styles = ["colonial", "ranch", "victorian"]
    cars = ["tesla model 3", "toyota camry", "ford f150"]

    # Iterate over all possible assignments using permutations
    for name_perm in itertools.permutations(names):
        # Constraint 7: Arnold is in the second house.
        if name_perm[1] != "Arnold":
            continue
        # Constraint 1: Peter is somewhere to the right of Eric.
        if name_perm.index("Peter") <= name_perm.index("Eric"):
            continue

        for phone_perm in itertools.permutations(phones):
            # Constraint 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
            valid_phone_order = False
            for i in range(2):
                if phone_perm[i] == "iphone 13" and phone_perm[i+1] == "google pixel 6":
                    valid_phone_order = True
                    break
            if not valid_phone_order:
                continue

            for height_perm in itertools.permutations(heights):
                # Constraint 9: The person who has an average height is in the first house.
                if height_perm[0] != "average":
                    continue

                for style_perm in itertools.permutations(house_styles):
                    # Constraint 2: The person living in a colonial-style house is in the second house.
                    if style_perm[1] != "colonial":
                        continue
                    # Constraint 6: The colonial-style house is somewhere to the right of the ranch-style home.
                    if style_perm.index("ranch") >= style_perm.index("colonial"):
                        continue

                    for car_perm in itertools.permutations(cars):
                        # Constraint 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
                        if car_perm.index("ford f150") <= car_perm.index("toyota camry"):
                            continue

                        # Constraint 3: The person who owns a Tesla Model 3 is the person who is very short.
                        tesla_valid = True
                        for i in range(3):
                            if car_perm[i] == "tesla model 3" and height_perm[i] != "very short":
                                tesla_valid = False
                                break
                            if height_perm[i] == "very short" and car_perm[i] != "tesla model 3":
                                tesla_valid = False
                                break
                        if not tesla_valid:
                            continue

                        # Constraint 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
                        index_short = height_perm.index("short")
                        if index_short == 2:  # Cannot be in the rightmost house
                            continue
                        if phone_perm[index_short + 1] != "samsung galaxy s21":
                            continue

                        # All constraints satisfied, construct the solution.
                        solution = {
                            "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                            "rows": [
                                ["1", name_perm[0], phone_perm[0], height_perm[0], style_perm[0], car_perm[0]],
                                ["2", name_perm[1], phone_perm[1], height_perm[1], style_perm[1], car_perm[1]],
                                ["3", name_perm[2], phone_perm[2], height_perm[2], style_perm[2], car_perm[2]]
                            ]
                        }
                        print(json.dumps({"solution": solution}, indent=2))
                        return

if __name__ == "__main__":
    main()