import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables: house numbers 1-5
    houses = [1, 2, 3, 4, 5]
    
    # Define domains for each attribute
    names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities = ["german", "swede", "norwegian", "dane", "brit"]
    
    # Add variables for each house - need separate variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"smoothie_{house}", smoothies)
        problem.addVariable(f"nationality_{house}", nationalities)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), [f"name_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"smoothie_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"nationality_{house}" for house in houses])
    
    # Helper function to get value for a specific house
    def get_house_value(solution, prefix, house):
        return solution.get(f"{prefix}_{house}")
    
    # Clue 1: The Dragonfruit smoothie lover is somewhere to the left of Eric
    def dragonfruit_left_of_eric(*args):
        # args contains all name and smoothie variables
        solution_dict = {}
        for i, house in enumerate(houses):
            solution_dict[f"name_{house}"] = args[i]
            solution_dict[f"smoothie_{house}"] = args[i + len(houses)]
        
        dragonfruit_house = None
        eric_house = None
        for house in houses:
            if get_house_value(solution_dict, "smoothie", house) == "dragonfruit":
                dragonfruit_house = house
            if get_house_value(solution_dict, "name", house) == "Eric":
                eric_house = house
        return dragonfruit_house is not None and eric_house is not None and dragonfruit_house < eric_house
    
    # Clue 2: The Dragonfruit smoothie lover is in the second house
    def dragonfruit_second(smoothie_2):
        return smoothie_2 == "dragonfruit"
    
    # Clue 3: Peter is not in the first house
    def peter_not_first(name_1):
        return name_1 != "Peter"
    
    # Clue 4: The Dane and the British person are next to each other
    def dane_brit_adjacent(*args):
        solution_dict = {}
        for i, house in enumerate(houses):
            solution_dict[f"nationality_{house}"] = args[i]
        
        dane_house = None
        brit_house = None
        for house in houses:
            if get_house_value(solution_dict, "nationality", house) == "dane":
                dane_house = house
            if get_house_value(solution_dict, "nationality", house) == "brit":
                brit_house = house
        return dane_house is not None and brit_house is not None and abs(dane_house - brit_house) == 1
    
    # Clue 5: The Desert smoothie lover is not in the fifth house
    def desert_not_fifth(smoothie_5):
        return smoothie_5 != "desert"
    
    # Clue 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover
    def swede_left_of_dragonfruit(*args):
        solution_dict = {}
        for i, house in enumerate(houses):
            solution_dict[f"nationality_{house}"] = args[i]
            solution_dict[f"smoothie_{house}"] = args[i + len(houses)]
        
        swede_house = None
        dragonfruit_house = None
        for house in houses:
            if get_house_value(solution_dict, "nationality", house) == "swede":
                swede_house = house
            if get_house_value(solution_dict, "smoothie", house) == "dragonfruit":
                dragonfruit_house = house
        return swede_house is not None and dragonfruit_house is not None and swede_house < dragonfruit_house
    
    # Clue 7: There are two houses between the person who drinks Lime smoothies and the Dane
    def lime_dane_two_houses(*args):
        solution_dict = {}
        for i, house in enumerate(houses):
            solution_dict[f"smoothie_{house}"] = args[i]
            solution_dict[f"nationality_{house}"] = args[i + len(houses)]
        
        lime_house = None
        dane_house = None
        for house in houses:
            if get_house_value(solution_dict, "smoothie", house) == "lime":
                lime_house = house
            if get_house_value(solution_dict, "nationality", house) == "dane":
                dane_house = house
        return lime_house is not None and dane_house is not None and abs(lime_house - dane_house) == 3
    
    # Clue 8: Bob is the Dane
    def bob_is_dane(*args):
        solution_dict = {}
        for i, house in enumerate(houses):
            solution_dict[f"name_{house}"] = args[i]
            solution_dict[f"nationality_{house}"] = args[i + len(houses)]
        
        for house in houses:
            if get_house_value(solution_dict, "name", house) == "Bob":
                return get_house_value(solution_dict, "nationality", house) == "dane"
        return False
    
    # Clue 9: Alice is the Norwegian
    def alice_is_norwegian(*args):
        solution_dict = {}
        for i, house in enumerate(houses):
            solution_dict[f"name_{house}"] = args[i]
            solution_dict[f"nationality_{house}"] = args[i + len(houses)]
        
        for house in houses:
            if get_house_value(solution_dict, "name", house) == "Alice":
                return get_house_value(solution_dict, "nationality", house) == "norwegian"
        return False
    
    # Clue 10: Alice is in the third house
    def alice_third(name_3):
        return name_3 == "Alice"
    
    # Clue 11: The Watermelon smoothie lover is in the third house
    def watermelon_third(smoothie_3):
        return smoothie_3 == "watermelon"
    
    # Add all constraints
    problem.addConstraint(dragonfruit_left_of_eric, [f"name_{house}" for house in houses] + [f"smoothie_{house}" for house in houses])
    problem.addConstraint(dragonfruit_second, ["smoothie_2"])
    problem.addConstraint(peter_not_first, ["name_1"])
    problem.addConstraint(dane_brit_adjacent, [f"nationality_{house}" for house in houses])
    problem.addConstraint(desert_not_fifth, ["smoothie_5"])
    problem.addConstraint(swede_left_of_dragonfruit, [f"nationality_{house}" for house in houses] + [f"smoothie_{house}" for house in houses])
    problem.addConstraint(lime_dane_two_houses, [f"smoothie_{house}" for house in houses] + [f"nationality_{house}" for house in houses])
    problem.addConstraint(bob_is_dane, [f"name_{house}" for house in houses] + [f"nationality_{house}" for house in houses])
    problem.addConstraint(alice_is_norwegian, [f"name_{house}" for house in houses] + [f"nationality_{house}" for house in houses])
    problem.addConstraint(alice_third, ["name_3"])
    problem.addConstraint(watermelon_third, ["smoothie_3"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Smoothie", "Nationality"], "rows": []}}
    
    # Convert solution to the required format
    solution = solutions[0]
    
    rows = []
    for house in houses:
        name = solution.get(f"name_{house}")
        smoothie = solution.get(f"smoothie_{house}")
        nationality = solution.get(f"nationality_{house}")
        rows.append([str(house), name, smoothie, nationality])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))