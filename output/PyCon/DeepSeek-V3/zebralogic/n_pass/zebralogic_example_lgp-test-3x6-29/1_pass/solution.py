import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3]
    
    # Define variables for each attribute
    names = ["Arnold", "Peter", "Eric"]
    animals = ["bird", "horse", "cat"]
    birthdays = ["jan", "sept", "april"]
    hobbies = ["photography", "cooking", "gardening"]
    drinks = ["milk", "water", "tea"]
    hair_colors = ["black", "brown", "blonde"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"animal_{house}", animals)
        problem.addVariable(f"birthday_{house}", birthdays)
        problem.addVariable(f"hobby_{house}", hobbies)
        problem.addVariable(f"drink_{house}", drinks)
        problem.addVariable(f"hair_color_{house}", hair_colors)
    
    # All attributes must be different within each category
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"name_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"animal_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"birthday_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"hobby_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"drink_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"hair_color_{house}" for house in houses])
    
    # Clue 1: The person who has brown hair is the person who loves cooking.
    for house in houses:
        problem.addConstraint(
            lambda hair, hobby, h=house: not (hair == "brown" and hobby != "cooking") and 
                                        not (hobby == "cooking" and hair != "brown"),
            [f"hair_color_{house}", f"hobby_{house}"]
        )
    
    # Clue 2: The person whose birthday is in April is in the third house.
    problem.addConstraint(lambda b: b == "april", ["birthday_3"])
    
    # Clue 3: Eric is not in the first house.
    problem.addConstraint(lambda n: n != "Eric", ["name_1"])
    
    # Clue 4: The cat lover is in the second house.
    problem.addConstraint(lambda a: a == "cat", ["animal_2"])
    
    # Clue 5: The person who has blonde hair is somewhere to the left of the person who likes milk.
    def left_of_blonde_milk(h1, h2, h3, d1, d2, d3):
        blonde_houses = []
        milk_houses = []
        for i, (hair, drink) in enumerate([(h1, d1), (h2, d2), (h3, d3)], 1):
            if hair == "blonde":
                blonde_houses.append(i)
            if drink == "milk":
                milk_houses.append(i)
        return all(any(blonde < milk for milk in milk_houses) for blonde in blonde_houses)
    
    problem.addConstraint(left_of_blonde_milk, 
                         [f"hair_color_{house}" for house in houses] + 
                         [f"drink_{house}" for house in houses])
    
    # Clue 6: The person who enjoys gardening is the person who likes milk.
    for house in houses:
        problem.addConstraint(
            lambda hobby, drink, h=house: not (hobby == "gardening" and drink != "milk") and 
                                        not (drink == "milk" and hobby != "gardening"),
            [f"hobby_{house}", f"drink_{house}"]
        )
    
    # Clue 7: The cat lover is the person who has brown hair.
    for house in houses:
        problem.addConstraint(
            lambda animal, hair, h=house: not (animal == "cat" and hair != "brown") and 
                                        not (hair == "brown" and animal != "cat"),
            [f"animal_{house}", f"hair_color_{house}"]
        )
    
    # Clue 8: Arnold is the bird keeper.
    for house in houses:
        problem.addConstraint(
            lambda name, animal, h=house: not (name == "Arnold" and animal != "bird") and 
                                        not (animal == "bird" and name != "Arnold"),
            [f"name_{house}", f"animal_{house}"]
        )
    
    # Clue 9: The one who only drinks water is the photography enthusiast.
    for house in houses:
        problem.addConstraint(
            lambda drink, hobby, h=house: not (drink == "water" and hobby != "photography") and 
                                        not (hobby == "photography" and drink != "water"),
            [f"drink_{house}", f"hobby_{house}"]
        )
    
    # Clue 10: The person whose birthday is in September is directly left of Arnold.
    def sept_left_of_arnold(b1, b2, b3, n1, n2, n3):
        arnold_house = None
        sept_house = None
        for i, (birthday, name) in enumerate([(b1, n1), (b2, n2), (b3, n3)], 1):
            if name == "Arnold":
                arnold_house = i
            if birthday == "sept":
                sept_house = i
        return sept_house is not None and arnold_house is not None and sept_house + 1 == arnold_house
    
    problem.addConstraint(sept_left_of_arnold, 
                         [f"birthday_{house}" for house in houses] + 
                         [f"name_{house}" for house in houses])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the output structure
    header = ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"animal_{house}"],
            solution[f"birthday_{house}"],
            solution[f"hobby_{house}"],
            solution[f"drink_{house}"],
            solution[f"hair_color_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))