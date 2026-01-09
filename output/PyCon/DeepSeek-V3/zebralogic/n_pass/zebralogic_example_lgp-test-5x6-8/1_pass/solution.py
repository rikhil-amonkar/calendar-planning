import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    houses = [1, 2, 3, 4, 5]
    names = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
    house_styles = ["modern", "craftsman", "ranch", "victorian", "colonial"]
    mothers = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
    phone_models = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
    drinks = ["coffee", "water", "root beer", "tea", "milk"]
    animals = ["fish", "dog", "horse", "bird", "cat"]
    
    # Add variables for each attribute per house
    problem.addVariables(["name"], names)
    problem.addVariables(["style"], house_styles)
    problem.addVariables(["mother"], mothers)
    problem.addVariables(["phone"], phone_models)
    problem.addVariables(["drink"], drinks)
    problem.addVariables(["animal"], animals)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), ["name"])
    problem.addConstraint(AllDifferentConstraint(), ["style"])
    problem.addConstraint(AllDifferentConstraint(), ["mother"])
    problem.addConstraint(AllDifferentConstraint(), ["phone"])
    problem.addConstraint(AllDifferentConstraint(), ["drink"])
    problem.addConstraint(AllDifferentConstraint(), ["animal"])
    
    # Clue 1: The person who uses a Google Pixel 6 is not in the first house.
    problem.addConstraint(lambda phone: phone != "google pixel 6", ["phone_1"])
    
    # Clue 2: The one who only drinks water is Alice.
    problem.addConstraint(lambda name, drink: not (drink == "water") or (name == "Alice"), ["name", "drink"])
    
    # Clue 3: The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
    def colonial_right_of_huawei(style1, style2, style3, style4, style5, phone1, phone2, phone3, phone4, phone5):
        huawei_house = None
        colonial_house = None
        for i, (style, phone) in enumerate([(style1, phone1), (style2, phone2), (style3, phone3), (style4, phone4), (style5, phone5)]):
            if phone == "huawei p50":
                huawei_house = i + 1
            if style == "colonial":
                colonial_house = i + 1
        return colonial_house > huawei_house
    
    problem.addConstraint(colonial_right_of_huawei, 
                         ["style_1", "style_2", "style_3", "style_4", "style_5",
                          "phone_1", "phone_2", "phone_3", "phone_4", "phone_5"])
    
    # Clue 4: The person who keeps horses is the person who uses a OnePlus 9.
    problem.addConstraint(lambda animal, phone: not (animal == "horse") or (phone == "oneplus 9"), ["animal", "phone"])
    
    # Clue 5: The person in a ranch-style home is The person whose mother's name is Kailyn.
    problem.addConstraint(lambda style, mother: not (style == "ranch") or (mother == "Kailyn"), ["style", "mother"])
    
    # Clue 6: The root beer lover is the cat lover.
    problem.addConstraint(lambda drink, animal: not (drink == "root beer") or (animal == "cat"), ["drink", "animal"])
    
    # Clue 7: The person living in a colonial-style house is not in the fourth house.
    problem.addConstraint(lambda style: style != "colonial", ["style_4"])
    
    # Clue 8: The bird keeper is in the fourth house.
    problem.addConstraint(lambda animal: animal == "bird", ["animal_4"])
    
    # Clue 9: The tea drinker is Bob.
    problem.addConstraint(lambda name, drink: not (drink == "tea") or (name == "Bob"), ["name", "drink"])
    
    # Clue 10: The tea drinker is somewhere to the right of The person whose mother's name is Kailyn.
    def tea_right_of_kailyn(mother1, mother2, mother3, mother4, mother5, drink1, drink2, drink3, drink4, drink5):
        kailyn_house = None
        tea_house = None
        for i, (mother, drink) in enumerate([(mother1, drink1), (mother2, drink2), (mother3, drink3), (mother4, drink4), (mother5, drink5)]):
            if mother == "Kailyn":
                kailyn_house = i + 1
            if drink == "tea":
                tea_house = i + 1
        return tea_house > kailyn_house
    
    problem.addConstraint(tea_right_of_kailyn,
                         ["mother_1", "mother_2", "mother_3", "mother_4", "mother_5",
                          "drink_1", "drink_2", "drink_3", "drink_4", "drink_5"])
    
    # Clue 11: The root beer lover is somewhere to the left of The person whose mother's name is Kailyn.
    def rootbeer_left_of_kailyn(mother1, mother2, mother3, mother4, mother5, drink1, drink2, drink3, drink4, drink5):
        kailyn_house = None
        rootbeer_house = None
        for i, (mother, drink) in enumerate([(mother1, drink1), (mother2, drink2), (mother3, drink3), (mother4, drink4), (mother5, drink5)]):
            if mother == "Kailyn":
                kailyn_house = i + 1
            if drink == "root beer":
                rootbeer_house = i + 1
        return rootbeer_house < kailyn_house
    
    problem.addConstraint(rootbeer_left_of_kailyn,
                         ["mother_1", "mother_2", "mother_3", "mother_4", "mother_5",
                          "drink_1", "drink_2", "drink_3", "drink_4", "drink_5"])
    
    # Clue 12: The person who keeps horses is the person in a modern-style house.
    problem.addConstraint(lambda animal, style: not (animal == "horse") or (style == "modern"), ["animal", "style"])
    
    # Clue 13: The person who uses an iPhone 13 is the person who likes milk.
    problem.addConstraint(lambda phone, drink: not (phone == "iphone 13") or (drink == "milk"), ["phone", "drink"])
    
    # Clue 14: The dog owner is the person who likes milk.
    problem.addConstraint(lambda animal, drink: not (animal == "dog") or (drink == "milk"), ["animal", "drink"])
    
    # Clue 15: The person who uses a Google Pixel 6 is the person in a Craftsman-style house.
    problem.addConstraint(lambda phone, style: not (phone == "google pixel 6") or (style == "craftsman"), ["phone", "style"])
    
    # Clue 16: Eric is not in the second house.
    problem.addConstraint(lambda name: name != "Eric", ["name_2"])
    
    # Clue 17: The tea drinker is in the fourth house.
    problem.addConstraint(lambda drink: drink == "tea", ["drink_4"])
    
    # Clue 18: The person who keeps horses is in the third house.
    problem.addConstraint(lambda animal: animal == "horse", ["animal_3"])
    
    # Clue 19: The person in a modern-style house is The person whose mother's name is Penny.
    problem.addConstraint(lambda style, mother: not (style == "modern") or (mother == "Penny"), ["style", "mother"])
    
    # Clue 20: The root beer lover is Peter.
    problem.addConstraint(lambda name, drink: not (drink == "root beer") or (name == "Peter"), ["name", "drink"])
    
    # Clue 21: The person whose mother's name is Aniya is not in the fourth house.
    problem.addConstraint(lambda mother: mother != "Aniya", ["mother_4"])
    
    # Clue 22: The person whose mother's name is Janelle is the one who only drinks water.
    problem.addConstraint(lambda mother, drink: not (mother == "Janelle") or (drink == "water"), ["mother", "drink"])
    
    # Get all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Convert to the required format
    solution = solutions[0]
    header = ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"]
    rows = []
    
    for house in range(1, 6):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"style_{house}"],
            solution[f"mother_{house}"],
            solution[f"phone_{house}"],
            solution[f"drink_{house}"],
            solution[f"animal_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))