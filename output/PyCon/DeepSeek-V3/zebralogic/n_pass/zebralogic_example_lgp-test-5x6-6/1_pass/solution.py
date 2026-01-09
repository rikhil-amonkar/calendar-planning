import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    houses = [1, 2, 3, 4, 5]
    
    # All possible values for each attribute
    names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
    vacations = ["mountain", "city", "cruise", "beach", "camping"]
    educations = ["doctorate", "high school", "bachelor", "associate", "master"]
    colors = ["blue", "red", "white", "yellow", "green"]
    phones = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
    foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"vacation_{house}", vacations)
        problem.addVariable(f"education_{house}", educations)
        problem.addVariable(f"color_{house}", colors)
        problem.addVariable(f"phone_{house}", phones)
        problem.addVariable(f"food_{house}", foods)
    
    # All attributes must be unique
    problem.addConstraint(AllDifferentConstraint(), [f"name_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"vacation_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"education_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"color_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"phone_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"food_{h}" for h in houses])
    
    # Clue 1: The person who loves the stew is not in the first house.
    problem.addConstraint(lambda food: food != "stew", ["food_1"])
    
    # Clue 2: There are two houses between the person who loves stir fry and the person with an associate's degree.
    def two_houses_between_food_education(food1, food2, food3, food4, food5, edu1, edu2, edu3, edu4, edu5):
        food_houses = [i+1 for i, food in enumerate([food1, food2, food3, food4, food5]) if food == "stir fry"]
        edu_houses = [i+1 for i, edu in enumerate([edu1, edu2, edu3, edu4, edu5]) if edu == "associate"]
        if food_houses and edu_houses:
            return abs(food_houses[0] - edu_houses[0]) == 3
        return False
    problem.addConstraint(two_houses_between_food_education, 
                         ["food_1", "food_2", "food_3", "food_4", "food_5",
                          "education_1", "education_2", "education_3", "education_4", "education_5"])
    
    # Clue 3: The person who enjoys mountain retreats is the person with a bachelor's degree.
    def same_house_vacation_education(vacation, education):
        return (vacation == "mountain") == (education == "bachelor")
    for house in houses:
        problem.addConstraint(same_house_vacation_education, [f"vacation_{house}", f"education_{house}"])
    
    # Clue 4: The person with a doctorate is somewhere to the right of Bob.
    def doctorate_right_of_bob(name1, name2, name3, name4, name5, edu1, edu2, edu3, edu4, edu5):
        bob_house = None
        doctorate_house = None
        for i, (name, edu) in enumerate(zip([name1, name2, name3, name4, name5], 
                                           [edu1, edu2, edu3, edu4, edu5])):
            if name == "Bob":
                bob_house = i + 1
            if edu == "doctorate":
                doctorate_house = i + 1
        if bob_house and doctorate_house:
            return doctorate_house > bob_house
        return False
    problem.addConstraint(doctorate_right_of_bob, 
                         ["name_1", "name_2", "name_3", "name_4", "name_5",
                          "education_1", "education_2", "education_3", "education_4", "education_5"])
    
    # Clue 5: The person who uses a Samsung Galaxy S21 is in the third house.
    problem.addConstraint(lambda phone: phone == "samsung galaxy s21", ["phone_3"])
    
    # Clue 6: Eric is the person with a doctorate.
    def eric_is_doctorate(name, education):
        return (name == "Eric") == (education == "doctorate")
    for house in houses:
        problem.addConstraint(eric_is_doctorate, [f"name_{house}", f"education_{house}"])
    
    # Clue 7: The person with a doctorate is in the third house.
    problem.addConstraint(lambda education: education == "doctorate", ["education_3"])
    
    # Clue 8: The person who loves stir fry is the person with a bachelor's degree.
    def stir_fry_is_bachelor(food, education):
        return (food == "stir fry") == (education == "bachelor")
    for house in houses:
        problem.addConstraint(stir_fry_is_bachelor, [f"food_{house}", f"education_{house}"])
    
    # Clue 9: The person with a doctorate is the person who is a pizza lover.
    def doctorate_is_pizza_lover(education, food):
        return (education == "doctorate") == (food == "pizza")
    for house in houses:
        problem.addConstraint(doctorate_is_pizza_lover, [f"education_{house}", f"food_{house}"])
    
    # Clue 10: The person whose favorite color is green is somewhere to the right of Peter.
    def green_right_of_peter(name1, name2, name3, name4, name5, color1, color2, color3, color4, color5):
        peter_house = None
        green_house = None
        for i, (name, color) in enumerate(zip([name1, name2, name3, name4, name5], 
                                             [color1, color2, color3, color4, color5])):
            if name == "Peter":
                peter_house = i + 1
            if color == "green":
                green_house = i + 1
        if peter_house and green_house:
            return green_house > peter_house
        return False
    problem.addConstraint(green_right_of_peter, 
                         ["name_1", "name_2", "name_3", "name_4", "name_5",
                          "color_1", "color_2", "color_3", "color_4", "color_5"])
    
    # Clue 11: The person who enjoys camping trips is the person who uses an iPhone 13.
    def camping_is_iphone(vacation, phone):
        return (vacation == "camping") == (phone == "iphone 13")
    for house in houses:
        problem.addConstraint(camping_is_iphone, [f"vacation_{house}", f"phone_{house}"])
    
    # Clue 12: The person who likes going on cruises is Alice.
    def cruise_is_alice(vacation, name):
        return (vacation == "cruise") == (name == "Alice")
    for house in houses:
        problem.addConstraint(cruise_is_alice, [f"vacation_{house}", f"name_{house}"])
    
    # Clue 13: There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
    def one_house_between_highschool_samsung(edu1, edu2, edu3, edu4, edu5):
        highschool_houses = [i+1 for i, edu in enumerate([edu1, edu2, edu3, edu4, edu5]) if edu == "high school"]
        samsung_house = 3  # From clue 5
        if highschool_houses:
            return abs(highschool_houses[0] - samsung_house) == 2
        return False
    problem.addConstraint(one_house_between_highschool_samsung, 
                         ["education_1", "education_2", "education_3", "education_4", "education_5"])
    
    # Clue 14: The person who uses a Google Pixel 6 is Arnold.
    def pixel_is_arnold(phone, name):
        return (phone == "google pixel 6") == (name == "Arnold")
    for house in houses:
        problem.addConstraint(pixel_is_arnold, [f"phone_{house}", f"name_{house}"])
    
    # Clue 15: The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
    def oneplus_right_of_huawei(phone1, phone2, phone3, phone4, phone5):
        huawei_house = None
        oneplus_house = None
        for i, phone in enumerate([phone1, phone2, phone3, phone4, phone5]):
            if phone == "huawei p50":
                huawei_house = i + 1
            if phone == "oneplus 9":
                oneplus_house = i + 1
        if huawei_house and oneplus_house:
            return oneplus_house > huawei_house
        return False
    problem.addConstraint(oneplus_right_of_huawei, 
                         ["phone_1", "phone_2", "phone_3", "phone_4", "phone_5"])
    
    # Clue 16: Arnold is the person who loves eating grilled cheese.
    def arnold_is_grilled_cheese(name, food):
        return (name == "Arnold") == (food == "grilled cheese")
    for house in houses:
        problem.addConstraint(arnold_is_grilled_cheese, [f"name_{house}", f"food_{house}"])
    
    # Clue 17: The person who loves eating grilled cheese is not in the fourth house.
    problem.addConstraint(lambda food: food != "grilled cheese", ["food_4"])
    
    # Clue 18: There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
    def two_houses_between_bachelor_red(edu1, edu2, edu3, edu4, edu5, color1, color2, color3, color4, color5):
        bachelor_houses = [i+1 for i, edu in enumerate([edu1, edu2, edu3, edu4, edu5]) if edu == "bachelor"]
        red_houses = [i+1 for i, color in enumerate([color1, color2, color3, color4, color5]) if color == "red"]
        if bachelor_houses and red_houses:
            return abs(bachelor_houses[0] - red_houses[0]) == 3
        return False
    problem.addConstraint(two_houses_between_bachelor_red, 
                         ["education_1", "education_2", "education_3", "education_4", "education_5",
                          "color_1", "color_2", "color_3", "color_4", "color_5"])
    
    # Clue 19: The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
    def beach_right_of_city(vacation1, vacation2, vacation3, vacation4, vacation5):
        city_house = None
        beach_house = None
        for i, vacation in enumerate([vacation1, vacation2, vacation3, vacation4, vacation5]):
            if vacation == "city":
                city_house = i + 1
            if vacation == "beach":
                beach_house = i + 1
        if city_house and beach_house:
            return beach_house > city_house
        return False
    problem.addConstraint(beach_right_of_city, 
                         ["vacation_1", "vacation_2", "vacation_3", "vacation_4", "vacation_5"])
    
    # Clue 20: The person whose favorite color is green is not in the second house.
    problem.addConstraint(lambda color: color != "green", ["color_2"])
    
    # Clue 21: The person who loves blue is somewhere to the right of Peter.
    def blue_right_of_peter(name1, name2, name3, name4, name5, color1, color2, color3, color4, color5):
        peter_house = None
        blue_house = None
        for i, (name, color) in enumerate(zip([name1, name2, name3, name4, name5], 
                                             [color1, color2, color3, color4, color5])):
            if name == "Peter":
                peter_house = i + 1
            if color == "blue":
                blue_house = i + 1
        if peter_house and blue_house:
            return blue_house > peter_house
        return False
    problem.addConstraint(blue_right_of_peter, 
                         ["name_1", "name_2", "name_3", "name_4", "name_5",
                          "color_1", "color_2", "color_3", "color_4", "color_5"])
    
    # Clue 22: There is one house between the person who enjoys camping trips and the person who loves yellow.
    def one_house_between_camping_yellow(vacation1, vacation2, vacation3, vacation4, vacation5, color1, color2, color3, color4, color5):
        camping_houses = [i+1 for i, vacation in enumerate([vacation1, vacation2, vacation3, vacation4, vacation5]) if vacation == "camping"]
        yellow_houses = [i+1 for i, color in enumerate([color1, color2, color3, color4, color5]) if color == "yellow"]
        if camping_houses and yellow_houses:
            return abs(camping_houses[0] - yellow_houses[0]) == 2
        return False
    problem.addConstraint(one_house_between_camping_yellow, 
                         ["vacation_1", "vacation_2", "vacation_3", "vacation_4", "vacation_5",
                          "color_1", "color_2", "color_3", "color_4", "color_5"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Format the solution
    header = ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"vacation_{house}"],
            solution[f"education_{house}"],
            solution[f"color_{house}"],
            solution[f"phone_{house}"],
            solution[f"food_{house}"]
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))