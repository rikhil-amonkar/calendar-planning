import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables: houses 1-4
    houses = [1, 2, 3, 4]
    
    # Define domains for each attribute
    names = ["Eric", "Peter", "Alice", "Arnold"]
    cars = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
    birthdays = ["jan", "april", "sept", "feb"]
    hobbies = ["painting", "cooking", "gardening", "photography"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"car_{house}", cars)
        problem.addVariable(f"birthday_{house}", birthdays)
        problem.addVariable(f"hobby_{house}", hobbies)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), [f"name_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"car_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"birthday_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"hobby_{house}" for house in houses])
    
    # Clue 1: The person whose birthday is in January is not in the second house.
    problem.addConstraint(lambda birthday_2: birthday_2 != "jan", ["birthday_2"])
    
    # Clue 2: The photography enthusiast is somewhere to the left of Eric.
    def left_of(target_hobby, target_name, h1, h2, h3, h4, n1, n2, n3, n4):
        hobby_positions = {h1: 1, h2: 2, h3: 3, h4: 4}
        name_positions = {n1: 1, n2: 2, n3: 3, n4: 4}
        hobby_house = None
        name_house = None
        for house, hobby in hobby_positions.items():
            if hobby == target_hobby:
                hobby_house = house
        for house, name in name_positions.items():
            if name == target_name:
                name_house = house
        return hobby_house < name_house if hobby_house and name_house else False
    problem.addConstraint(left_of, ["photography", "Eric", 
                                   "hobby_1", "hobby_2", "hobby_3", "hobby_4",
                                   "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 3: The photography enthusiast is somewhere to the left of Peter.
    problem.addConstraint(left_of, ["photography", "Peter", 
                                   "hobby_1", "hobby_2", "hobby_3", "hobby_4",
                                   "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 4: The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
    def directly_left(c1, c2, c3, c4):
        for i in range(1, 4):
            car_left = locals()[f"c{i}"]
            car_right = locals()[f"c{i+1}"]
            if car_left == "honda civic" and car_right == "tesla model 3":
                return True
        return False
    problem.addConstraint(directly_left, ["car_1", "car_2", "car_3", "car_4"])
    
    # Clue 5: There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
    def one_house_between(c1, c2, c3, c4, h1, h2, h3, h4):
        tesla_pos = None
        gardening_pos = None
        cars = {1: c1, 2: c2, 3: c3, 4: c4}
        hobbies = {1: h1, 2: h2, 3: h3, 4: h4}
        
        for house, car in cars.items():
            if car == "tesla model 3":
                tesla_pos = house
        for house, hobby in hobbies.items():
            if hobby == "gardening":
                gardening_pos = house
                
        return abs(tesla_pos - gardening_pos) == 2 if tesla_pos and gardening_pos else False
    problem.addConstraint(one_house_between, 
                         ["car_1", "car_2", "car_3", "car_4", 
                          "hobby_1", "hobby_2", "hobby_3", "hobby_4"])
    
    # Clue 6: The person who owns a Tesla Model 3 is Arnold.
    def same_person_for_tesla_arnold(c1, c2, c3, c4, n1, n2, n3, n4):
        for i in range(1, 5):
            car = locals()[f"c{i}"]
            name = locals()[f"n{i}"]
            if car == "tesla model 3" and name == "Arnold":
                return True
        return False
    problem.addConstraint(same_person_for_tesla_arnold, 
                         ["car_1", "car_2", "car_3", "car_4",
                          "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 7: The person whose birthday is in February is the person who loves cooking.
    def same_person_for_feb_cooking(b1, b2, b3, b4, h1, h2, h3, h4):
        for i in range(1, 5):
            birthday = locals()[f"b{i}"]
            hobby = locals()[f"h{i}"]
            if birthday == "feb" and hobby == "cooking":
                return True
        return False
    problem.addConstraint(same_person_for_feb_cooking, 
                         ["birthday_1", "birthday_2", "birthday_3", "birthday_4",
                          "hobby_1", "hobby_2", "hobby_3", "hobby_4"])
    
    # Clue 8: The person who owns a Toyota Camry is Peter.
    def same_person_for_toyota_peter(c1, c2, c3, c4, n1, n2, n3, n4):
        for i in range(1, 5):
            car = locals()[f"c{i}"]
            name = locals()[f"n{i}"]
            if car == "toyota camry" and name == "Peter":
                return True
        return False
    problem.addConstraint(same_person_for_toyota_peter, 
                         ["car_1", "car_2", "car_3", "car_4",
                          "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 9: The person whose birthday is in April is Arnold.
    def same_person_for_april_arnold(b1, b2, b3, b4, n1, n2, n3, n4):
        for i in range(1, 5):
            birthday = locals()[f"b{i}"]
            name = locals()[f"n{i}"]
            if birthday == "april" and name == "Arnold":
                return True
        return False
    problem.addConstraint(same_person_for_april_arnold, 
                         ["birthday_1", "birthday_2", "birthday_3", "birthday_4",
                          "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 10: Alice is the photography enthusiast.
    def same_person_for_alice_photography(n1, n2, n3, n4, h1, h2, h3, h4):
        for i in range(1, 5):
            name = locals()[f"n{i}"]
            hobby = locals()[f"h{i}"]
            if name == "Alice" and hobby == "photography":
                return True
        return False
    problem.addConstraint(same_person_for_alice_photography, 
                         ["name_1", "name_2", "name_3", "name_4",
                          "hobby_1", "hobby_2", "hobby_3", "hobby_4"])
    
    # Clue 11: Peter is the person whose birthday is in January.
    def same_person_for_peter_jan(n1, n2, n3, n4, b1, b2, b3, b4):
        for i in range(1, 5):
            name = locals()[f"n{i}"]
            birthday = locals()[f"b{i}"]
            if name == "Peter" and birthday == "jan":
                return True
        return False
    problem.addConstraint(same_person_for_peter_jan, 
                         ["name_1", "name_2", "name_3", "name_4",
                          "birthday_1", "birthday_2", "birthday_3", "birthday_4"])
    
    # Solve the puzzle
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "CarModel", "Birthday", "Hobby"], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        car = solution[f"car_{house}"]
        birthday = solution[f"birthday_{house}"]
        hobby = solution[f"hobby_{house}"]
        rows.append([str(house), name, car, birthday, hobby])
    
    result = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))