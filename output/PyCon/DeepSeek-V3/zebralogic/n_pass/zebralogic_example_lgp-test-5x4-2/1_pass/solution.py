import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']
    houses = [1, 2, 3, 4, 5]
    
    # Add variables for each attribute per house
    problem.addVariables(["name1", "name2", "name3", "name4", "name5"], names)
    problem.addVariables(["color1", "color2", "color3", "color4", "color5"], colors)
    problem.addVariables(["phone1", "phone2", "phone3", "phone4", "phone5"], phones)
    problem.addVariables(["occupation1", "occupation2", "occupation3", "occupation4", "occupation5"], occupations)
    
    # All attributes must be different within their category
    problem.addConstraint(AllDifferentConstraint(), ["name1", "name2", "name3", "name4", "name5"])
    problem.addConstraint(AllDifferentConstraint(), ["color1", "color2", "color3", "color4", "color5"])
    problem.addConstraint(AllDifferentConstraint(), ["phone1", "phone2", "phone3", "phone4", "phone5"])
    problem.addConstraint(AllDifferentConstraint(), ["occupation1", "occupation2", "occupation3", "occupation4", "occupation5"])
    
    # Clue 2: Bob is in the second house
    problem.addConstraint(lambda name2: name2 == 'Bob', ["name2"])
    
    # Clue 3: The person who uses a Samsung Galaxy S21 is the person who is a doctor
    for i in houses:
        problem.addConstraint(
            lambda phone, occupation, i=i: not (phone == 'samsung galaxy s21') or (occupation == 'doctor'),
            [f"phone{i}", f"occupation{i}"]
        )
    
    # Clue 4: The person who is a doctor is the person who loves blue
    for i in houses:
        problem.addConstraint(
            lambda occupation, color, i=i: not (occupation == 'doctor') or (color == 'blue'),
            [f"occupation{i}", f"color{i}"]
        )
    
    # Clue 5: The person whose favorite color is green is not in the fifth house
    problem.addConstraint(lambda color5: color5 != 'green', ["color5"])
    
    # Clue 6: The person who is a lawyer is the person who uses a OnePlus 9
    for i in houses:
        problem.addConstraint(
            lambda occupation, phone, i=i: not (occupation == 'lawyer') or (phone == 'oneplus 9'),
            [f"occupation{i}", f"phone{i}"]
        )
    
    # Clue 7: The person who loves blue is directly left of the person whose favorite color is red
    for i in range(1, 5):
        problem.addConstraint(
            lambda color_i, color_j, i=i: not (color_i == 'blue') or (color_j == 'red'),
            [f"color{i}", f"color{i+1}"]
        )
    
    # Clue 8: The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21
    for i in houses:
        for j in houses:
            if j <= i:
                problem.addConstraint(
                    lambda phone_i, occupation_j, i=i, j=j: not (phone_i == 'samsung galaxy s21' and occupation_j == 'lawyer') or (j > i),
                    [f"phone{i}", f"occupation{j}"]
                )
    
    # Clue 9: There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50
    for i in houses:
        for j in houses:
            if abs(i - j) != 2:
                problem.addConstraint(
                    lambda phone_i, phone_j, i=i, j=j: not (phone_i == 'google pixel 6' and phone_j == 'huawei p50'),
                    [f"phone{i}", f"phone{j}"]
                )
    
    # Clue 10: Arnold is the person who is an engineer
    for i in houses:
        problem.addConstraint(
            lambda name, occupation, i=i: not (name == 'Arnold') or (occupation == 'engineer'),
            [f"name{i}", f"occupation{i}"]
        )
    
    # Clue 11: Alice is the person who loves yellow
    for i in houses:
        problem.addConstraint(
            lambda name, color, i=i: not (name == 'Alice') or (color == 'yellow'),
            [f"name{i}", f"color{i}"]
        )
    
    # Clue 12: The person who uses a Google Pixel 6 is Eric
    for i in houses:
        problem.addConstraint(
            lambda phone, name, i=i: not (phone == 'google pixel 6') or (name == 'Eric'),
            [f"phone{i}", f"name{i}"]
        )
    
    # Clue 13: The person who uses a Google Pixel 6 is the person who is a teacher
    for i in houses:
        problem.addConstraint(
            lambda phone, occupation, i=i: not (phone == 'google pixel 6') or (occupation == 'teacher'),
            [f"phone{i}", f"occupation{i}"]
        )
    
    # Clue 14: The person whose favorite color is red is somewhere to the right of the person who is a teacher
    for i in houses:
        for j in houses:
            if j <= i:
                problem.addConstraint(
                    lambda occupation_i, color_j, i=i, j=j: not (occupation_i == 'teacher' and color_j == 'red') or (j > i),
                    [f"occupation{i}", f"color{j}"]
                )
    
    # Clue 1: The person who is an engineer is somewhere to the right of the person who is a lawyer
    for i in houses:
        for j in houses:
            if j <= i:
                problem.addConstraint(
                    lambda occupation_i, occupation_j, i=i, j=j: not (occupation_i == 'engineer' and occupation_j == 'lawyer') or (i > j),
                    [f"occupation{i}", f"occupation{j}"]
                )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    result = {
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": []
        }
    }
    
    for i in range(1, 6):
        row = [
            str(i),
            solution[f"name{i}"],
            solution[f"color{i}"],
            solution[f"phone{i}"],
            solution[f"occupation{i}"]
        ]
        result["solution"]["rows"].append(row)
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))