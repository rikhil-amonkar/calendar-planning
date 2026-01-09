import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define domains for each attribute
    names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
    styles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
    foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
    vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
    heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
    cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"style_{house}", styles)
        problem.addVariable(f"food_{house}", foods)
        problem.addVariable(f"vacation_{house}", vacations)
        problem.addVariable(f"height_{house}", heights)
        problem.addVariable(f"cigar_{house}", cigars)
    
    # All attributes must be different
    for attr in ["name", "style", "food", "vacation", "height", "cigar"]:
        problem.addConstraint(AllDifferentConstraint(), [f"{attr}_{house}" for house in houses])
    
    # Clue 1: Alice is in the fifth house.
    problem.addConstraint(lambda name: name == "Alice", ["name_5"])
    
    # Clue 2: The person who loves stir fry is the person living in a colonial-style house.
    for house in houses:
        problem.addConstraint(
            lambda food, style, h=house: not (food == "stir fry" and style != "colonial") and not (style == "colonial" and food != "stir fry"),
            [f"food_{house}", f"style_{house}"]
        )
    
    # Clue 3: Alice is the person who loves the spaghetti eater.
    # This means Alice's food is spaghetti
    problem.addConstraint(lambda food: food == "spaghetti", ["food_5"])
    
    # Clue 4: Arnold is the person who loves the stew.
    for house in houses:
        problem.addConstraint(
            lambda name, food, h=house: not (name == "Arnold" and food != "stew") and not (food == "stew" and name != "Arnold"),
            [f"name_{house}", f"food_{house}"]
        )
    
    # Clue 5: There is one house between the person who has an average height and Peter.
    for house in houses:
        for other_house in houses:
            if abs(house - other_house) == 2:
                problem.addConstraint(
                    lambda height, name, h1=house, h2=other_house: not (height == "average" and name != "Peter") and not (name == "Peter" and height != "average"),
                    [f"height_{house}", f"name_{other_house}"]
                )
    
    # Clue 6: The person in a Craftsman-style house is not in the third house.
    problem.addConstraint(lambda style: style != "craftsman", ["style_3"])
    
    # Clue 7: The person who has an average height is the person who loves stir fry.
    for house in houses:
        problem.addConstraint(
            lambda height, food, h=house: not (height == "average" and food != "stir fry") and not (food == "stir fry" and height != "average"),
            [f"height_{house}", f"food_{house}"]
        )
    
    # Clue 8: The person who loves beach vacations is the person in a ranch-style home.
    for house in houses:
        problem.addConstraint(
            lambda vacation, style, h=house: not (vacation == "beach" and style != "ranch") and not (style == "ranch" and vacation != "beach"),
            [f"vacation_{house}", f"style_{house}"]
        )
    
    # Clue 9: Eric is in the fourth house.
    problem.addConstraint(lambda name: name == "Eric", ["name_4"])
    
    # Clue 10: There is one house between the person living in a colonial-style house and the person who enjoys camping trips.
    for house in houses:
        for other_house in houses:
            if abs(house - other_house) == 2:
                problem.addConstraint(
                    lambda style, vacation, h1=house, h2=other_house: not (style == "colonial" and vacation != "camping") and not (vacation == "camping" and style != "colonial"),
                    [f"style_{house}", f"vacation_{other_house}"]
                )
    
    # Clue 11: The person who enjoys mountain retreats is the person who smokes Yellow Monster.
    for house in houses:
        problem.addConstraint(
            lambda vacation, cigar, h=house: not (vacation == "mountain" and cigar != "yellow monster") and not (cigar == "yellow monster" and vacation != "mountain"),
            [f"vacation_{house}", f"cigar_{house}"]
        )
    
    # Clue 12: The person who enjoys mountain retreats is the person who is very tall.
    for house in houses:
        problem.addConstraint(
            lambda vacation, height, h=house: not (vacation == "mountain" and height != "very tall") and not (height == "very tall" and vacation != "mountain"),
            [f"vacation_{house}", f"height_{house}"]
        )
    
    # Clue 13: The person who enjoys mountain retreats and the Dunhill smoker are next to each other.
    for house in houses:
        for other_house in houses:
            if abs(house - other_house) == 1:
                problem.addConstraint(
                    lambda vacation, cigar, h1=house, h2=other_house: not (vacation == "mountain" and cigar != "dunhill") and not (cigar == "dunhill" and vacation != "mountain"),
                    [f"vacation_{house}", f"cigar_{other_house}"]
                )
    
    # Clue 14: The person who loves the spaghetti eater is the person residing in a Victorian house.
    # Since Alice loves spaghetti (clue 3), Alice is in Victorian house
    problem.addConstraint(lambda style: style == "victorian", ["style_5"])
    
    # Clue 15: The person who is tall is the person who loves beach vacations.
    for house in houses:
        problem.addConstraint(
            lambda height, vacation, h=house: not (height == "tall" and vacation != "beach") and not (vacation == "beach" and height != "tall"),
            [f"height_{house}", f"vacation_{house}"]
        )
    
    # Clue 16: The person who is tall is somewhere to the left of the person residing in a Victorian house.
    # Victorian house is house 5 (from clue 14), so tall person must be in house 1-4
    for house in [5, 6]:
        problem.addConstraint(lambda height: height != "tall", [f"height_{house}"])
    
    # Clue 17: The person who loves stir fry is directly left of Bob.
    for house in range(1, 6):
        problem.addConstraint(
            lambda food, name, h=house: not (food == "stir fry" and name != "Bob") and not (name == "Bob" and food != "stir fry"),
            [f"food_{house}", f"name_{house+1}"]
        )
    
    # Clue 18: The person in a modern-style house is somewhere to the left of Alice.
    # Alice is in house 5, so modern must be in house 1-4
    for house in [5, 6]:
        problem.addConstraint(lambda style: style != "modern", [f"style_{house}"])
    
    # Clue 19: The person in a Craftsman-style house is somewhere to the left of the person who is short.
    for short_house in houses:
        for craftsman_house in houses:
            if craftsman_house >= short_house:
                problem.addConstraint(
                    lambda style, height, h1=craftsman_house, h2=short_house: not (style == "craftsman" and height == "short"),
                    [f"style_{craftsman_house}", f"height_{short_house}"]
                )
    
    # Clue 20: The person who loves stir fry is somewhere to the left of the Prince smoker.
    for stir_fry_house in houses:
        for prince_house in houses:
            if stir_fry_house >= prince_house:
                problem.addConstraint(
                    lambda food, cigar, h1=stir_fry_house, h2=prince_house: not (food == "stir fry" and cigar == "prince"),
                    [f"food_{stir_fry_house}", f"cigar_{prince_house}"]
                )
    
    # Clue 21: There are two houses between the person who loves eating grilled cheese and the person who is super tall.
    for house in houses:
        for other_house in houses:
            if abs(house - other_house) == 3:
                problem.addConstraint(
                    lambda food, height, h1=house, h2=other_house: not (food == "grilled cheese" and height != "super tall") and not (height == "super tall" and food != "grilled cheese"),
                    [f"food_{house}", f"height_{other_house}"]
                )
    
    # Clue 22: The person in a ranch-style home is the person who smokes Blue Master.
    for house in houses:
        problem.addConstraint(
            lambda style, cigar, h=house: not (style == "ranch" and cigar != "blue master") and not (cigar == "blue master" and style != "ranch"),
            [f"style_{house}", f"cigar_{house}"]
        )
    
    # Clue 23: The person who smokes many unique blends is directly left of the person who smokes Blue Master.
    for house in range(1, 6):
        problem.addConstraint(
            lambda cigar1, cigar2, h=house: not (cigar1 == "blends" and cigar2 != "blue master") and not (cigar2 == "blue master" and cigar1 != "blends"),
            [f"cigar_{house}", f"cigar_{house+1}"]
        )
    
    # Clue 24: The person who goes on cultural tours is the person who is a pizza lover.
    for house in houses:
        problem.addConstraint(
            lambda vacation, food, h=house: not (vacation == "cultural" and food != "pizza") and not (food == "pizza" and vacation != "cultural"),
            [f"vacation_{house}", f"food_{house}"]
        )
    
    # Clue 25: The person who is a pizza lover is somewhere to the left of the person who likes going on cruises.
    for pizza_house in houses:
        for cruise_house in houses:
            if pizza_house >= cruise_house:
                problem.addConstraint(
                    lambda food, vacation, h1=pizza_house, h2=cruise_house: not (food == "pizza" and vacation == "cruise"),
                    [f"food_{pizza_house}", f"vacation_{cruise_house}"]
                )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
            "rows": []
        }
    }
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"style_{house}"],
            solution[f"food_{house}"],
            solution[f"vacation_{house}"],
            solution[f"height_{house}"],
            solution[f"cigar_{house}"]
        ]
        result["solution"]["rows"].append(row)
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))