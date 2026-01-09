import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
    birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
    foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
    heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
    car_models = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"birthday_{house}", birthdays)
        problem.addVariable(f"food_{house}", foods)
        problem.addVariable(f"height_{house}", heights)
        problem.addVariable(f"car_{house}", car_models)
    
    # All attributes must be different
    for attr in ["name", "birthday", "food", "height", "car"]:
        problem.addConstraint(AllDifferentConstraint(), [f"{attr}_{house}" for house in houses])
    
    # Clue 1: The person who owns a Honda Civic is the person who is short.
    for house in houses:
        problem.addConstraint(
            lambda car, height: not (car == "honda civic") or (height == "short"),
            [f"car_{house}", f"height_{house}"]
        )
        problem.addConstraint(
            lambda car, height: not (height == "short") or (car == "honda civic"),
            [f"car_{house}", f"height_{house}"]
        )
    
    # Clue 2: The person who owns a Ford F-150 is in the fifth house.
    problem.addConstraint(lambda car: car == "ford f150", ["car_5"])
    
    # Clue 3: The person who loves stir fry is somewhere to the left of Eric.
    for house_eric in houses:
        problem.addConstraint(
            lambda food, eric_house=house_eric: not (food == "stir fry") or (eric_house > 1),
            [f"food_{house_eric}"]
        )
        for house_stirfry in houses:
            if house_stirfry >= house_eric:
                problem.addConstraint(
                    lambda food_sf, food_er, sf_house=house_stirfry, er_house=house_eric: 
                    not (food_sf == "stir fry" and food_er == "Eric") or (sf_house < er_house),
                    [f"food_{house_stirfry}", f"name_{house_eric}"]
                )
    
    # Clue 4: The person whose birthday is in May is somewhere to the left of Carol.
    for house_carol in houses:
        problem.addConstraint(
            lambda birthday, carol_house=house_carol: not (birthday == "may") or (carol_house > 1),
            [f"birthday_{house_carol}"]
        )
        for house_may in houses:
            if house_may >= house_carol:
                problem.addConstraint(
                    lambda bday_m, name_c, may_house=house_may, carol_house=house_carol: 
                    not (bday_m == "may" and name_c == "Carol") or (may_house < carol_house),
                    [f"birthday_{house_may}", f"name_{house_carol}"]
                )
    
    # Clue 5: The person who is very short is somewhere to the left of the person whose birthday is in April.
    for house_april in houses:
        problem.addConstraint(
            lambda height, april_house=house_april: not (height == "very short") or (april_house > 1),
            [f"height_{house_april}"]
        )
        for house_vshort in houses:
            if house_vshort >= house_april:
                problem.addConstraint(
                    lambda height_vs, bday_a, vs_house=house_vshort, april_house=house_april: 
                    not (height_vs == "very short" and bday_a == "april") or (vs_house < april_house),
                    [f"height_{house_vshort}", f"birthday_{house_april}"]
                )
    
    # Clue 6: The person who owns a BMW 3 Series is not in the third house.
    problem.addConstraint(lambda car: car != "bmw 3 series", ["car_3"])
    
    # Clue 7: There are two houses between the person who loves stir fry and the person who is a pizza lover.
    for house1 in houses:
        for house2 in houses:
            if abs(house1 - house2) == 3:
                problem.addConstraint(
                    lambda food1, food2: (food1 == "stir fry" and food2 == "pizza") or 
                                        (food1 == "pizza" and food2 == "stir fry"),
                    [f"food_{house1}", f"food_{house2}"]
                )
    
    # Clue 8: The person who loves the soup is directly left of Eric.
    for house in houses:
        if house < 6:
            problem.addConstraint(
                lambda food, name_next: not (food == "soup") or (name_next == "Eric"),
                [f"food_{house}", f"name_{house+1}"]
            )
    
    # Clue 9: The person who loves the spaghetti eater and the person whose birthday is in May are next to each other.
    for house in houses:
        neighbors = []
        if house > 1:
            neighbors.append(house-1)
        if house < 6:
            neighbors.append(house+1)
        
        for neighbor in neighbors:
            problem.addConstraint(
                lambda food, bday, food_n, bday_n: not (food == "spaghetti" and bday_n == "may") or True,
                [f"food_{house}", f"birthday_{house}", f"food_{neighbor}", f"birthday_{neighbor}"]
            )
            problem.addConstraint(
                lambda food, bday, food_n, bday_n: not (bday == "may" and food_n == "spaghetti") or True,
                [f"birthday_{house}", f"food_{house}", f"birthday_{neighbor}", f"food_{neighbor}"]
            )
    
    # Clue 10: Alice is directly left of the person who owns a BMW 3 Series.
    for house in houses:
        if house < 6:
            problem.addConstraint(
                lambda name, car_next: not (name == "Alice") or (car_next == "bmw 3 series"),
                [f"name_{house}", f"car_{house+1}"]
            )
    
    # Clue 11: The person who owns a Tesla Model 3 is somewhere to the left of the person who is tall.
    for house_tall in houses:
        problem.addConstraint(
            lambda car, tall_house=house_tall: not (car == "tesla model 3") or (tall_house > 1),
            [f"car_{house_tall}"]
        )
        for house_tesla in houses:
            if house_tesla >= house_tall:
                problem.addConstraint(
                    lambda car_t, height_t, tesla_house=house_tesla, tall_house=house_tall: 
                    not (car_t == "tesla model 3" and height_t == "tall") or (tesla_house < tall_house),
                    [f"car_{house_tesla}", f"height_{house_tall}"]
                )
    
    # Clue 12: The person who is very tall is the person who owns a Toyota Camry.
    for house in houses:
        problem.addConstraint(
            lambda height, car: not (height == "very tall") or (car == "toyota camry"),
            [f"height_{house}", f"car_{house}"]
        )
        problem.addConstraint(
            lambda height, car: not (car == "toyota camry") or (height == "very tall"),
            [f"height_{house}", f"car_{house}"]
        )
    
    # Clue 13: Peter is directly left of the person who is a pizza lover.
    for house in houses:
        if house < 6:
            problem.addConstraint(
                lambda name, food_next: not (name == "Peter") or (food_next == "pizza"),
                [f"name_{house}", f"food_{house+1}"]
            )
    
    # Clue 14: The person who loves the stew is not in the third house.
    problem.addConstraint(lambda food: food != "stew", ["food_3"])
    
    # Clue 15: There is one house between the person whose birthday is in September and the person who is very short.
    for house1 in houses:
        for house2 in houses:
            if abs(house1 - house2) == 2:
                problem.addConstraint(
                    lambda bday1, height2: (bday1 == "sept" and height2 == "very short") or 
                                          (height2 == "very short" and bday1 == "sept"),
                    [f"birthday_{house1}", f"height_{house2}"]
                )
    
    # Clue 16: There is one house between the person whose birthday is in March and the person who is super tall.
    for house1 in houses:
        for house2 in houses:
            if abs(house1 - house2) == 2:
                problem.addConstraint(
                    lambda bday1, height2: (bday1 == "mar" and height2 == "super tall") or 
                                          (height2 == "super tall" and bday1 == "mar"),
                    [f"birthday_{house1}", f"height_{house2}"]
                )
    
    # Clue 17: The person who is tall is Bob.
    for house in houses:
        problem.addConstraint(
            lambda height, name: not (height == "tall") or (name == "Bob"),
            [f"height_{house}", f"name_{house}"]
        )
        problem.addConstraint(
            lambda height, name: not (name == "Bob") or (height == "tall"),
            [f"height_{house}", f"name_{house}"]
        )
    
    # Clue 18: The person whose birthday is in May is somewhere to the right of Alice.
    for house_alice in houses:
        problem.addConstraint(
            lambda birthday, alice_house=house_alice: not (birthday == "may") or (alice_house < 6),
            [f"birthday_{house_alice}"]
        )
        for house_may in houses:
            if house_may <= house_alice:
                problem.addConstraint(
                    lambda bday_m, name_a, may_house=house_may, alice_house=house_alice: 
                    not (bday_m == "may" and name_a == "Alice") or (may_house > alice_house),
                    [f"birthday_{house_may}", f"name_{house_alice}"]
                )
    
    # Clue 19: The person who is very short is in the fourth house.
    problem.addConstraint(lambda height: height == "very short", ["height_4"])
    
    # Clue 20: The person whose birthday is in March is the person who is short.
    for house in houses:
        problem.addConstraint(
            lambda birthday, height: not (birthday == "mar") or (height == "short"),
            [f"birthday_{house}", f"height_{house}"]
        )
        problem.addConstraint(
            lambda birthday, height: not (height == "short") or (birthday == "mar"),
            [f"birthday_{house}", f"height_{house}"]
        )
    
    # Clue 21: Carol is the person who owns a Tesla Model 3.
    for house in houses:
        problem.addConstraint(
            lambda name, car: not (name == "Carol") or (car == "tesla model 3"),
            [f"name_{house}", f"car_{house}"]
        )
        problem.addConstraint(
            lambda name, car: not (car == "tesla model 3") or (name == "Carol"),
            [f"name_{house}", f"car_{house}"]
        )
    
    # Clue 22: Eric is the person whose birthday is in January.
    for house in houses:
        problem.addConstraint(
            lambda name, birthday: not (name == "Eric") or (birthday == "jan"),
            [f"name_{house}", f"birthday_{house}"]
        )
        problem.addConstraint(
            lambda name, birthday: not (birthday == "jan") or (name == "Eric"),
            [f"name_{house}", f"birthday_{house}"]
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"], "rows": []}}
    
    solution = solutions[0]
    
    # Format the solution
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        birthday = solution[f"birthday_{house}"]
        food = solution[f"food_{house}"]
        height = solution[f"height_{house}"]
        car = solution[f"car_{house}"]
        rows.append([str(house), name, birthday, food, height, car])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))