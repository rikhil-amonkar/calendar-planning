import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    houses = [1, 2, 3]
    
    # Add variables for each attribute
    problem.addVariable("name", ["Eric", "Peter", "Arnold"])
    problem.addVariable("drink", ["tea", "water", "milk"])
    problem.addVariable("nationality", ["dane", "brit", "swede"])
    problem.addVariable("education", ["high school", "associate", "bachelor"])
    problem.addVariable("house_style", ["victorian", "colonial", "ranch"])
    problem.addVariable("smoothie", ["cherry", "watermelon", "desert"])
    
    # Add variables for house positions (1, 2, 3)
    problem.addVariable("house", houses)
    
    # All attributes must be different (each person has unique combination)
    problem.addConstraint(lambda n1, n2, n3: len({n1, n2, n3}) == 3, 
                         ["name_1", "name_2", "name_3"])
    problem.addConstraint(lambda d1, d2, d3: len({d1, d2, d3}) == 3, 
                         ["drink_1", "drink_2", "drink_3"])
    problem.addConstraint(lambda nat1, nat2, nat3: len({nat1, nat2, nat3}) == 3, 
                         ["nationality_1", "nationality_2", "nationality_3"])
    problem.addConstraint(lambda e1, e2, e3: len({e1, e2, e3}) == 3, 
                         ["education_1", "education_2", "education_3"])
    problem.addConstraint(lambda hs1, hs2, hs3: len({hs1, hs2, hs3}) == 3, 
                         ["house_style_1", "house_style_2", "house_style_3"])
    problem.addConstraint(lambda s1, s2, s3: len({s1, s2, s3}) == 3, 
                         ["smoothie_1", "smoothie_2", "smoothie_3"])
    
    # Create variables for each house position
    for house in houses:
        problem.addVariable(f"name_{house}", ["Eric", "Peter", "Arnold"])
        problem.addVariable(f"drink_{house}", ["tea", "water", "milk"])
        problem.addVariable(f"nationality_{house}", ["dane", "brit", "swede"])
        problem.addVariable(f"education_{house}", ["high school", "associate", "bachelor"])
        problem.addVariable(f"house_style_{house}", ["victorian", "colonial", "ranch"])
        problem.addVariable(f"smoothie_{house}", ["cherry", "watermelon", "desert"])
    
    # Clue 1: There is one house between Eric and the tea drinker.
    def clue1(eric_house, tea_house):
        return abs(eric_house - tea_house) == 2
    
    problem.addConstraint(clue1, ["eric_position", "tea_position"])
    
    # Clue 2: The person who likes milk is the person in a ranch-style home.
    for house in houses:
        problem.addConstraint(
            lambda milk, style, h=house: not (milk == "milk" and style != "ranch") and not (style == "ranch" and milk != "milk"),
            [f"drink_{house}", f"house_style_{house}"]
        )
    
    # Clue 3: The person with a bachelor's degree is in the second house.
    problem.addConstraint(lambda e: e == "bachelor", ["education_2"])
    
    # Clue 4: The person with a high school diploma is the Dane.
    for house in houses:
        problem.addConstraint(
            lambda edu, nat, h=house: not (edu == "high school" and nat != "dane") and not (nat == "dane" and edu != "high school"),
            [f"education_{house}", f"nationality_{house}"]
        )
    
    # Clue 5: The Desert smoothie lover is the Swedish person.
    for house in houses:
        problem.addConstraint(
            lambda smooth, nat, h=house: not (smooth == "desert" and nat != "swede") and not (nat == "swede" and smooth != "desert"),
            [f"smoothie_{house}", f"nationality_{house}"]
        )
    
    # Clue 6: The person residing in a Victorian house is not in the first house.
    problem.addConstraint(lambda style: style != "victorian", ["house_style_1"])
    
    # Clue 7: The person who likes Cherry smoothies is the person living in a colonial-style house.
    for house in houses:
        problem.addConstraint(
            lambda smooth, style, h=house: not (smooth == "cherry" and style != "colonial") and not (style == "colonial" and smooth != "cherry"),
            [f"smoothie_{house}", f"house_style_{house}"]
        )
    
    # Clue 8: Arnold is somewhere to the right of the person residing in a Victorian house.
    def clue8(arnold_pos, victorian_pos):
        return arnold_pos > victorian_pos
    
    problem.addConstraint(clue8, ["arnold_position", "victorian_position"])
    
    # Clue 9: The person in a ranch-style home is the person with a high school diploma.
    for house in houses:
        problem.addConstraint(
            lambda style, edu, h=house: not (style == "ranch" and edu != "high school") and not (edu == "high school" and style != "ranch"),
            [f"house_style_{house}", f"education_{house}"]
        )
    
    # Add position variables for specific people and attributes
    problem.addVariable("eric_position", houses)
    problem.addVariable("arnold_position", houses)
    problem.addVariable("tea_position", houses)
    problem.addVariable("victorian_position", houses)
    
    # Link position variables to actual attributes
    for house in houses:
        problem.addConstraint(
            lambda pos, name, h=house: not (pos == h and name != "Eric"),
            ["eric_position", f"name_{house}"]
        )
        problem.addConstraint(
            lambda pos, name, h=house: not (pos == h and name != "Arnold"),
            ["arnold_position", f"name_{house}"]
        )
        problem.addConstraint(
            lambda pos, drink, h=house: not (pos == h and drink != "tea"),
            ["tea_position", f"drink_{house}"]
        )
        problem.addConstraint(
            lambda pos, style, h=house: not (pos == h and style != "victorian"),
            ["victorian_position", f"house_style_{house}"]
        )
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"drink_{house}"],
            solution[f"nationality_{house}"],
            solution[f"education_{house}"],
            solution[f"house_style_{house}"],
            solution[f"smoothie_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))