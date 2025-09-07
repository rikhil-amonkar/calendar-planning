import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
    vacations = ["mountain", "city", "cruise", "beach", "camping"]
    educations = ["doctorate", "high school", "bachelor", "associate", "master"]
    colors = ["blue", "red", "white", "yellow", "green"]
    phones = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
    foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for vacation_perm in permutations(vacations):
            for education_perm in permutations(educations):
                for color_perm in permutations(colors):
                    for phone_perm in permutations(phones):
                        for food_perm in permutations(foods):
                            # Create assignment for each house (index 0-4)
                            assignment = []
                            for i in range(5):
                                house = {
                                    "House": i+1,
                                    "Name": name_perm[i],
                                    "Vacation": vacation_perm[i],
                                    "Education": education_perm[i],
                                    "Color": color_perm[i],
                                    "PhoneModel": phone_perm[i],
                                    "Food": food_perm[i]
                                }
                                assignment.append(house)
                            
                            # Check all constraints
                            if check_constraints(assignment):
                                output_solution(assignment)
                                return

def check_constraints(houses):
    # Convert to dict for easier access
    house_dict = {i+1: house for i, house in enumerate(houses)}
    
    # Clue 1: The person who loves the stew is not in the first house.
    if any(house["Food"] == "stew" and house["House"] == 1 for house in houses):
        return False
    
    # Clue 2: There are two houses between the person who loves stir fry and the person with an associate's degree.
    stir_fry_house = next(house["House"] for house in houses if house["Food"] == "stir fry")
    associate_house = next(house["House"] for house in houses if house["Education"] == "associate")
    if abs(stir_fry_house - associate_house) != 3:
        return False
    
    # Clue 3: The person who enjoys mountain retreats is the person with a bachelor's degree.
    if not any(house["Vacation"] == "mountain" and house["Education"] == "bachelor" for house in houses):
        return False
    
    # Clue 4: The person with a doctorate is somewhere to the right of Bob.
    bob_house = next(house["House"] for house in houses if house["Name"] == "Bob")
    doctorate_house = next(house["House"] for house in houses if house["Education"] == "doctorate")
    if doctorate_house <= bob_house:
        return False
    
    # Clue 5: The person who uses a Samsung Galaxy S21 is in the third house.
    if not any(house["PhoneModel"] == "samsung galaxy s21" and house["House"] == 3 for house in houses):
        return False
    
    # Clue 6: Eric is the person with a doctorate.
    if not any(house["Name"] == "Eric" and house["Education"] == "doctorate" for house in houses):
        return False
    
    # Clue 7: The person with a doctorate is in the third house.
    if not any(house["Education"] == "doctorate" and house["House"] == 3 for house in houses):
        return False
    
    # Clue 8: The person who loves stir fry is the person with a bachelor's degree.
    if not any(house["Food"] == "stir fry" and house["Education"] == "bachelor" for house in houses):
        return False
    
    # Clue 9: The person with a doctorate is the person who is a pizza lover.
    if not any(house["Education"] == "doctorate" and house["Food"] == "pizza" for house in houses):
        return False
    
    # Clue 10: The person whose favorite color is green is somewhere to the right of Peter.
    peter_house = next(house["House"] for house in houses if house["Name"] == "Peter")
    green_house = next(house["House"] for house in houses if house["Color"] == "green")
    if green_house <= peter_house:
        return False
    
    # Clue 11: The person who enjoys camping trips is the person who uses an iPhone 13.
    if not any(house["Vacation"] == "camping" and house["PhoneModel"] == "iphone 13" for house in houses):
        return False
    
    # Clue 12: The person who likes going on cruises is Alice.
    if not any(house["Vacation"] == "cruise" and house["Name"] == "Alice" for house in houses):
        return False
    
    # Clue 13: There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
    hs_house = next(house["House"] for house in houses if house["Education"] == "high school")
    samsung_house = next(house["House"] for house in houses if house["PhoneModel"] == "samsung galaxy s21")
    if abs(hs_house - samsung_house) != 2:
        return False
    
    # Clue 14: The person who uses a Google Pixel 6 is Arnold.
    if not any(house["PhoneModel"] == "google pixel 6" and house["Name"] == "Arnold" for house in houses):
        return False
    
    # Clue 15: The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
    oneplus_house = next(house["House"] for house in houses if house["PhoneModel"] == "oneplus 9")
    huawei_house = next(house["House"] for house in houses if house["PhoneModel"] == "huawei p50")
    if oneplus_house <= huawei_house:
        return False
    
    # Clue 16: Arnold is the person who loves eating grilled cheese.
    if not any(house["Name"] == "Arnold" and house["Food"] == "grilled cheese" for house in houses):
        return False
    
    # Clue 17: The person who loves eating grilled cheese is not in the fourth house.
    if any(house["Food"] == "grilled cheese" and house["House"] == 4 for house in houses):
        return False
    
    # Clue 18: There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
    bachelor_house = next(house["House"] for house in houses if house["Education"] == "bachelor")
    red_house = next(house["House"] for house in houses if house["Color"] == "red")
    if abs(bachelor_house - red_house) != 3:
        return False
    
    # Clue 19: The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
    beach_house = next(house["House"] for house in houses if house["Vacation"] == "beach")
    city_house = next(house["House"] for house in houses if house["Vacation"] == "city")
    if beach_house <= city_house:
        return False
    
    # Clue 20: The person whose favorite color is green is not in the second house.
    if any(house["Color"] == "green" and house["House"] == 2 for house in houses):
        return False
    
    # Clue 21: The person who loves blue is somewhere to the right of Peter.
    peter_house = next(house["House"] for house in houses if house["Name"] == "Peter")
    blue_house = next(house["House"] for house in houses if house["Color"] == "blue")
    if blue_house <= peter_house:
        return False
    
    # Clue 22: There is one house between the person who enjoys camping trips and the person who loves yellow.
    camping_house = next(house["House"] for house in houses if house["Vacation"] == "camping")
    yellow_house = next(house["House"] for house in houses if house["Color"] == "yellow")
    if abs(camping_house - yellow_house) != 2:
        return False
    
    return True

def output_solution(houses):
    # Sort houses by house number
    houses.sort(key=lambda x: x["House"])
    
    # Prepare the solution in the required format
    header = ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"]
    rows = []
    
    for house in houses:
        row = [
            str(house["House"]),
            house["Name"],
            house["Vacation"],
            house["Education"],
            house["Color"],
            house["PhoneModel"],
            house["Food"]
        ]
        rows.append(row)
    
    solution = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()