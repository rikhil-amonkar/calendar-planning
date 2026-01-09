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
    def left_of_photography_eric(h1, h2, h3, h4, n1, n2, n3, n4):
        hobby_positions = {1: h1, 2: h2, 3: h3, 4: h4}
        name_positions = {1: n1, 2: n2, 3: n3, 4: n4}
        
        photography_house = None
        eric_house = None
        
        for house, hobby in hobby_positions.items():
            if hobby == "photography":
                photography_house = house
                
        for house, name in name_positions.items():
            if name == "Eric":
                eric_house = house
                
        return photography_house is not None and eric_house is not None and photography_house < eric_house
    
    problem.addConstraint(left_of_photography_eric, 
                         ["hobby_1", "hobby_2", "hobby_3", "hobby_4",
                          "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 3: The photography enthusiast is somewhere to the left of Peter.
    def left_of_photography_peter(h1, h2, h3, h4, n1, n2, n3, n4):
        hobby_positions = {1: h1, 2: h2, 3: h3, 4: h4}
        name_positions = {1: n1, 2: n2, 3: n3, 4: n4}
        
        photography_house = None
        peter_house = None
        
        for house, hobby in hobby_positions.items():
            if hobby == "photography":
                photography_house = house
                
        for house, name in name_positions.items():
            if name == "Peter":
                peter_house = house
                
        return photography_house is not None and peter_house is not None and photography_house < peter_house
    
    problem.addConstraint(left_of_photography_peter, 
                         ["hobby_1", "hobby_2", "hobby_3", "hobby_4",
                          "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 4: The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
    def directly_left_honda_tesla(c1, c2, c3, c4):
        cars = {1: c1, 2: c2, 3: c3, 4: c4}
        
        for i in range(1, 4):
            if cars[i] == "honda civic" and cars[i+1] == "tesla model 3":
                return True
        return False
    
    problem.addConstraint(directly_left_honda_tesla, ["car_1", "car_2", "car_3", "car_4"])
    
    # Clue 5: There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
    def one_house_between_tesla_gardening(c1, c2, c3, c4, h1, h2, h3, h4):
        cars = {1: c1, 2: c2, 3: c3, 4: c4}
        hobbies = {1: h1, 2: h2, 3: h3, 4: h4}
        
        tesla_pos = None
        gardening_pos = None
        
        for house, car in cars.items():
            if car == "tesla model 3":
                tesla_pos = house
                
        for house, hobby in hobbies.items():
            if hobby == "gardening":
                gardening_pos = house
                
        return tesla_pos is not None and gardening_pos is not None and abs(tesla_pos - gardening_pos) == 2
    
    problem.addConstraint(one_house_between_tesla_gardening, 
                         ["car_1", "car_2", "car_3", "car_4", 
                          "hobby_1", "hobby_2", "hobby_3", "hobby_4"])
    
    # Clue 6: The person who owns a Tesla Model 3 is Arnold.
    def tesla_is_arnold(c1, c2, c3, c4, n1, n2, n3, n4):
        cars = {1: c1, 2: c2, 3: c3, 4: c4}
        names = {1: n1, 2: n2, 3: n3, 4: n4}
        
        for house, car in cars.items():
            if car == "tesla model 3":
                return names[house] == "Arnold"
        return False
    
    problem.addConstraint(tesla_is_arnold, 
                         ["car_1", "car_2", "car_3", "car_4",
                          "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 7: The person whose birthday is in February is the person who loves cooking.
    def feb_is_cooking(b1, b2, b3, b4, h1, h2, h3, h4):
        birthdays_dict = {1: b1, 2: b2, 3: b3, 4: b4}
        hobbies_dict = {1: h1, 2: h2, 3: h3, 4: h4}
        
        for house, birthday in birthdays_dict.items():
            if birthday == "feb":
                return hobbies_dict[house] == "cooking"
        return False
    
    problem.addConstraint(feb_is_cooking, 
                         ["birthday_1", "birthday_2", "birthday_3", "birthday_4",
                          "hobby_1", "hobby_2", "hobby_3", "hobby_4"])
    
    # Clue 8: The person who owns a Toyota Camry is Peter.
    def toyota_is_peter(c1, c2, c3, c4, n1, n2, n3, n4):
        cars_dict = {1: c1, 2: c2, 3: c3, 4: c4}
        names_dict = {1: n1, 2: n2, 3: n3, 4: n4}
        
        for house, car in cars_dict.items():
            if car == "toyota camry":
                return names_dict[house] == "Peter"
        return False
    
    problem.addConstraint(toyota_is_peter, 
                         ["car_1", "car_2", "car_3", "car_4",
                          "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 9: The person whose birthday is in April is Arnold.
    def april_is_arnold(b1, b2, b3, b4, n1, n2, n3, n4):
        birthdays_dict = {1: b1, 2: b2, 3: b3, 4: b4}
        names_dict = {1: n1, 2: n2, 3: n3, 4: n4}
        
        for house, birthday in birthdays_dict.items():
            if birthday == "april":
                return names_dict[house] == "Arnold"
        return False
    
    problem.addConstraint(april_is_arnold, 
                         ["birthday_1", "birthday_2", "birthday_3", "birthday_4",
                          "name_1", "name_2", "name_3", "name_4"])
    
    # Clue 10: Alice is the photography enthusiast.
    def alice_is_photography(n1, n2, n3, n4, h1, h2, h3, h4):
        names_dict = {1: n1, 2: n2, 3: n3, 4: n4}
        hobbies_dict = {1: h1, 2: h2, 3: h3, 4: h4}
        
        for house, name in names_dict.items():
            if name == "Alice":
                return hobbies_dict[house] == "photography"
        return False
    
    problem.addConstraint(alice_is_photography, 
                         ["name_1", "name_2", "name_3", "name_4",
                          "hobby_1", "hobby_2", "hobby_3", "hobby_4"])
    
    # Clue 11: Peter is the person whose birthday is in January.
    def peter_is_jan(n1, n2, n3, n4, b1, b2, b3, b4):
        names_dict = {1: n1, 2: n2, 3: n3, 4: n4}
        birthdays_dict = {1: b1, 2: b2, 3: b3, 4: b4}
        
        for house, name in names_dict.items():
            if name == "Peter":
                return birthdays_dict[house] == "jan"
        return False
    
    problem.addConstraint(peter_is_jan, 
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