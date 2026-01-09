import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define domains for each attribute
    names = ["Eric", "Arnold", "Peter"]
    vacations = ["mountain", "city", "beach"]
    heights = ["very short", "short", "average"]
    flowers = ["carnations", "daffodils", "lilies"]
    hair_colors = ["brown", "black", "blonde"]
    educations = ["associate", "bachelor", "high school"]
    
    # Add variables for each attribute per house
    problem.addVariables(["name1", "name2", "name3"], names)
    problem.addVariables(["vacation1", "vacation2", "vacation3"], vacations)
    problem.addVariables(["height1", "height2", "height3"], heights)
    problem.addVariables(["flower1", "flower2", "flower3"], flowers)
    problem.addVariables(["hair1", "hair2", "hair3"], hair_colors)
    problem.addVariables(["education1", "education2", "education3"], educations)
    
    # All attributes must be different within their category
    problem.addConstraint(AllDifferentConstraint(), ["name1", "name2", "name3"])
    problem.addConstraint(AllDifferentConstraint(), ["vacation1", "vacation2", "vacation3"])
    problem.addConstraint(AllDifferentConstraint(), ["height1", "height2", "height3"])
    problem.addConstraint(AllDifferentConstraint(), ["flower1", "flower2", "flower3"])
    problem.addConstraint(AllDifferentConstraint(), ["hair1", "hair2", "hair3"])
    problem.addConstraint(AllDifferentConstraint(), ["education1", "education2", "education3"])
    
    # Clue 1: Peter is the person who has an average height.
    def peter_average_height(n1, n2, n3, h1, h2, h3):
        if n1 == "Peter":
            return h1 == "average"
        if n2 == "Peter":
            return h2 == "average"
        if n3 == "Peter":
            return h3 == "average"
        return False
    problem.addConstraint(peter_average_height, ["name1", "name2", "name3", "height1", "height2", "height3"])
    
    # Clue 2: The person who loves a bouquet of daffodils is Arnold.
    def arnold_daffodils(n1, n2, n3, f1, f2, f3):
        if n1 == "Arnold":
            return f1 == "daffodils"
        if n2 == "Arnold":
            return f2 == "daffodils"
        if n3 == "Arnold":
            return f3 == "daffodils"
        return False
    problem.addConstraint(arnold_daffodils, ["name1", "name2", "name3", "flower1", "flower2", "flower3"])
    
    # Clue 3: The person who is very short is not in the second house.
    problem.addConstraint(lambda h2: h2 != "very short", ["height2"])
    
    # Clue 4: The person who loves beach vacations is in the first house.
    problem.addConstraint(lambda v1: v1 == "beach", ["vacation1"])
    
    # Clue 5: The person with a high school diploma is in the third house.
    problem.addConstraint(lambda e3: e3 == "high school", ["education3"])
    
    # Clue 6: The person who is short is somewhere to the right of the person who is very short.
    def short_right_of_very_short(h1, h2, h3):
        very_short_pos = None
        short_pos = None
        if h1 == "very short":
            very_short_pos = 1
        if h2 == "very short":
            very_short_pos = 2
        if h3 == "very short":
            very_short_pos = 3
            
        if h1 == "short":
            short_pos = 1
        if h2 == "short":
            short_pos = 2
        if h3 == "short":
            short_pos = 3
            
        return very_short_pos is not None and short_pos is not None and short_pos > very_short_pos
    problem.addConstraint(short_right_of_very_short, ["height1", "height2", "height3"])
    
    # Clue 7: The person who loves the bouquet of lilies is Eric.
    def eric_lilies(n1, n2, n3, f1, f2, f3):
        if n1 == "Eric":
            return f1 == "lilies"
        if n2 == "Eric":
            return f2 == "lilies"
        if n3 == "Eric":
            return f3 == "lilies"
        return False
    problem.addConstraint(eric_lilies, ["name1", "name2", "name3", "flower1", "flower2", "flower3"])
    
    # Clue 8: The person who loves the bouquet of lilies is the person with a bachelor's degree.
    def lilies_bachelor(f1, f2, f3, e1, e2, e3):
        if f1 == "lilies":
            return e1 == "bachelor"
        if f2 == "lilies":
            return e2 == "bachelor"
        if f3 == "lilies":
            return e3 == "bachelor"
        return False
    problem.addConstraint(lilies_bachelor, ["flower1", "flower2", "flower3", "education1", "education2", "education3"])
    
    # Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
    def city_right_of_peter(n1, n2, n3, v1, v2, v3):
        peter_pos = None
        city_pos = None
        if n1 == "Peter":
            peter_pos = 1
        if n2 == "Peter":
            peter_pos = 2
        if n3 == "Peter":
            peter_pos = 3
            
        if v1 == "city":
            city_pos = 1
        if v2 == "city":
            city_pos = 2
        if v3 == "city":
            city_pos = 3
            
        return peter_pos is not None and city_pos is not None and city_pos > peter_pos
    problem.addConstraint(city_right_of_peter, ["name1", "name2", "name3", "vacation1", "vacation2", "vacation3"])
    
    # Clue 10: The person who has blonde hair is in the third house.
    problem.addConstraint(lambda h3: h3 == "blonde", ["hair3"])
    
    # Clue 11: The person who loves beach vacations is the person who has brown hair.
    def beach_brown_hair(v1, v2, v3, h1, h2, h3):
        if v1 == "beach":
            return h1 == "brown"
        if v2 == "beach":
            return h2 == "brown"
        if v3 == "beach":
            return h3 == "brown"
        return False
    problem.addConstraint(beach_brown_hair, ["vacation1", "vacation2", "vacation3", "hair1", "hair2", "hair3"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f"name{house}"],
            solution[f"vacation{house}"],
            solution[f"height{house}"],
            solution[f"flower{house}"],
            solution[f"hair{house}"],
            solution[f"education{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))