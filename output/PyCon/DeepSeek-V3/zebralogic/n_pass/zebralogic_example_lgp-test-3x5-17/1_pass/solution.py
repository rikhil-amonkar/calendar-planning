import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1, 2, 3)
    houses = [1, 2, 3]
    
    # Define domains for each attribute
    names = ["Eric", "Arnold", "Peter"]
    phones = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
    heights = ["very short", "average", "short"]
    styles = ["colonial", "ranch", "victorian"]
    cars = ["tesla model 3", "toyota camry", "ford f150"]
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"phone_{house}", phones)
        problem.addVariable(f"height_{house}", heights)
        problem.addVariable(f"style_{house}", styles)
        problem.addVariable(f"car_{house}", cars)
    
    # All attributes must be different across houses
    problem.addConstraint(AllDifferentConstraint(), [f"name_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"phone_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"height_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"style_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"car_{h}" for h in houses])
    
    # Clue 1: Peter is somewhere to the right of Eric
    def peter_right_of_eric(*args):
        eric_pos = None
        peter_pos = None
        for i, name in enumerate(args):
            if name == "Eric":
                eric_pos = i + 1
            if name == "Peter":
                peter_pos = i + 1
        return peter_pos > eric_pos
    problem.addConstraint(peter_right_of_eric, [f"name_{h}" for h in houses])
    
    # Clue 2: The person living in a colonial-style house is in the second house
    problem.addConstraint(lambda style: style == "colonial", ["style_2"])
    
    # Clue 3: The person who owns a Tesla Model 3 is the person who is very short
    for house in houses:
        problem.addConstraint(
            lambda car, height, h=house: not (car == "tesla model 3" and height != "very short"),
            [f"car_{house}", f"height_{house}"]
        )
        problem.addConstraint(
            lambda car, height, h=house: not (height == "very short" and car != "tesla model 3"),
            [f"car_{house}", f"height_{house}"]
        )
    
    # Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21
    problem.addConstraint(
        lambda height1, phone2: not (height1 == "short" and phone2 != "samsung galaxy s21"),
        ["height_1", "phone_2"]
    )
    problem.addConstraint(
        lambda height2, phone3: not (height2 == "short" and phone3 != "samsung galaxy s21"),
        ["height_2", "phone_3"]
    )
    
    # Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6
    problem.addConstraint(
        lambda phone1, phone2: not (phone1 == "iphone 13" and phone2 != "google pixel 6"),
        ["phone_1", "phone_2"]
    )
    problem.addConstraint(
        lambda phone2, phone3: not (phone2 == "iphone 13" and phone3 != "google pixel 6"),
        ["phone_2", "phone_3"]
    )
    
    # Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home
    def colonial_right_of_ranch(style1, style2, style3):
        ranch_pos = None
        colonial_pos = None
        styles = [style1, style2, style3]
        for i, style in enumerate(styles):
            if style == "ranch":
                ranch_pos = i + 1
            if style == "colonial":
                colonial_pos = i + 1
        return colonial_pos > ranch_pos
    problem.addConstraint(colonial_right_of_ranch, [f"style_{h}" for h in houses])
    
    # Clue 7: Arnold is in the second house
    problem.addConstraint(lambda name: name == "Arnold", ["name_2"])
    
    # Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry
    def ford_right_of_toyota(car1, car2, car3):
        toyota_pos = None
        ford_pos = None
        cars = [car1, car2, car3]
        for i, car in enumerate(cars):
            if car == "toyota camry":
                toyota_pos = i + 1
            if car == "ford f150":
                ford_pos = i + 1
        return ford_pos > toyota_pos
    problem.addConstraint(ford_right_of_toyota, [f"car_{h}" for h in houses])
    
    # Clue 9: The person who has an average height is in the first house
    problem.addConstraint(lambda height: height == "average", ["height_1"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Prepare the output
    header = ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"phone_{house}"],
            solution[f"height_{house}"],
            solution[f"style_{house}"],
            solution[f"car_{house}"]
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