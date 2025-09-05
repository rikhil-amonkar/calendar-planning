import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ["Eric", "Arnold", "Peter"]
    phones = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
    heights = ["very short", "average", "short"]
    house_styles = ["colonial", "ranch", "victorian"]
    car_models = ["tesla model 3", "toyota camry", "ford f150"]
    
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for phone_perm in permutations(phones):
            for height_perm in permutations(heights):
                for style_perm in permutations(house_styles):
                    for car_perm in permutations(car_models):
                        # Create assignment dictionaries
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                "Name": name_perm[i],
                                "PhoneModel": phone_perm[i],
                                "Height": height_perm[i],
                                "HouseStyle": style_perm[i],
                                "CarModel": car_perm[i]
                            }
                        
                        # Check all constraints
                        # Clue 1: Peter is somewhere to the right of Eric
                        peter_house = None
                        eric_house = None
                        for house, attrs in assignment.items():
                            if attrs["Name"] == "Peter":
                                peter_house = house
                            if attrs["Name"] == "Eric":
                                eric_house = house
                        if peter_house <= eric_house:
                            continue
                        
                        # Clue 2: The person living in a colonial-style house is in the second house
                        if assignment[2]["HouseStyle"] != "colonial":
                            continue
                        
                        # Clue 3: The person who owns a Tesla Model 3 is the person who is very short
                        clue3_satisfied = True
                        for house, attrs in assignment.items():
                            if attrs["CarModel"] == "tesla model 3" and attrs["Height"] != "very short":
                                clue3_satisfied = False
                                break
                            if attrs["Height"] == "very short" and attrs["CarModel"] != "tesla model 3":
                                clue3_satisfied = False
                                break
                        if not clue3_satisfied:
                            continue
                        
                        # Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21
                        short_house = None
                        samsung_house = None
                        for house, attrs in assignment.items():
                            if attrs["Height"] == "short":
                                short_house = house
                            if attrs["PhoneModel"] == "samsung galaxy s21":
                                samsung_house = house
                        if short_house is None or samsung_house is None or short_house + 1 != samsung_house:
                            continue
                        
                        # Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6
                        iphone_house = None
                        pixel_house = None
                        for house, attrs in assignment.items():
                            if attrs["PhoneModel"] == "iphone 13":
                                iphone_house = house
                            if attrs["PhoneModel"] == "google pixel 6":
                                pixel_house = house
                        if iphone_house is None or pixel_house is None or iphone_house + 1 != pixel_house:
                            continue
                        
                        # Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home
                        colonial_house = None
                        ranch_house = None
                        for house, attrs in assignment.items():
                            if attrs["HouseStyle"] == "colonial":
                                colonial_house = house
                            if attrs["HouseStyle"] == "ranch":
                                ranch_house = house
                        if colonial_house <= ranch_house:
                            continue
                        
                        # Clue 7: Arnold is in the second house
                        if assignment[2]["Name"] != "Arnold":
                            continue
                        
                        # Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry
                        ford_house = None
                        toyota_house = None
                        for house, attrs in assignment.items():
                            if attrs["CarModel"] == "ford f150":
                                ford_house = house
                            if attrs["CarModel"] == "toyota camry":
                                toyota_house = house
                        if ford_house <= toyota_house:
                            continue
                        
                        # Clue 9: The person who has an average height is in the first house
                        if assignment[1]["Height"] != "average":
                            continue
                        
                        # If we reach here, all constraints are satisfied
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                                "rows": []
                            }
                        }
                        
                        for house in sorted(assignment.keys()):
                            row = [
                                str(house),
                                assignment[house]["Name"],
                                assignment[house]["PhoneModel"],
                                assignment[house]["Height"],
                                assignment[house]["HouseStyle"],
                                assignment[house]["CarModel"]
                            ]
                            solution["solution"]["rows"].append(row)
                        
                        print(json.dumps(solution, indent=2))
                        return
    
    print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()