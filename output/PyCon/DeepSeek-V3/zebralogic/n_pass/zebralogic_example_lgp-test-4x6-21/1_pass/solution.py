import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-4)
    houses = [1, 2, 3, 4]
    
    # Define domains for each attribute
    names = ["Peter", "Arnold", "Alice", "Eric"]
    flowers = ["roses", "daffodils", "carnations", "lilies"]
    hobbies = ["photography", "painting", "cooking", "gardening"]
    pets = ["dog", "fish", "bird", "cat"]
    colors = ["red", "yellow", "green", "white"]
    house_styles = ["craftsman", "colonial", "ranch", "victorian"]
    
    # Add variables for each attribute per house
    problem.addVariables(["name1", "name2", "name3", "name4"], names)
    problem.addVariables(["flower1", "flower2", "flower3", "flower4"], flowers)
    problem.addVariables(["hobby1", "hobby2", "hobby3", "hobby4"], hobbies)
    problem.addVariables(["pet1", "pet2", "pet3", "pet4"], pets)
    problem.addVariables(["color1", "color2", "color3", "color4"], colors)
    problem.addVariables(["style1", "style2", "style3", "style4"], house_styles)
    
    # All attributes must have unique values per house
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ["name1", "name2", "name3", "name4"])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ["flower1", "flower2", "flower3", "flower4"])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ["hobby1", "hobby2", "hobby3", "hobby4"])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ["pet1", "pet2", "pet3", "pet4"])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ["color1", "color2", "color3", "color4"])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         ["style1", "style2", "style3", "style4"])
    
    # Clue 1: The person in a Craftsman-style house is Arnold.
    problem.addConstraint(lambda style, name: (style == "craftsman") == (name == "Arnold"),
                         ["style1", "name1"])
    problem.addConstraint(lambda style, name: (style == "craftsman") == (name == "Arnold"),
                         ["style2", "name2"])
    problem.addConstraint(lambda style, name: (style == "craftsman") == (name == "Arnold"),
                         ["style3", "name3"])
    problem.addConstraint(lambda style, name: (style == "craftsman") == (name == "Arnold"),
                         ["style4", "name4"])
    
    # Clue 2: The person who loves the rose bouquet is somewhere to the right of Peter.
    def rose_right_of_peter(n1, n2, n3, n4, f1, f2, f3, f4):
        peter_house = None
        rose_house = None
        if n1 == "Peter": peter_house = 1
        if n2 == "Peter": peter_house = 2
        if n3 == "Peter": peter_house = 3
        if n4 == "Peter": peter_house = 4
        if f1 == "roses": rose_house = 1
        if f2 == "roses": rose_house = 2
        if f3 == "roses": rose_house = 3
        if f4 == "roses": rose_house = 4
        return rose_house > peter_house
    
    problem.addConstraint(rose_right_of_peter, 
                         ["name1", "name2", "name3", "name4", "flower1", "flower2", "flower3", "flower4"])
    
    # Clue 3: The photography enthusiast is the person who owns a dog.
    problem.addConstraint(lambda h1, p1: (h1 == "photography") == (p1 == "dog"), ["hobby1", "pet1"])
    problem.addConstraint(lambda h2, p2: (h2 == "photography") == (p2 == "dog"), ["hobby2", "pet2"])
    problem.addConstraint(lambda h3, p3: (h3 == "photography") == (p3 == "dog"), ["hobby3", "pet3"])
    problem.addConstraint(lambda h4, p4: (h4 == "photography") == (p4 == "dog"), ["hobby4", "pet4"])
    
    # Clue 4: The person who loves a bouquet of daffodils is not in the fourth house.
    problem.addConstraint(lambda f4: f4 != "daffodils", ["flower4"])
    
    # Clue 5: The person who loves the rose bouquet is the person whose favorite color is red.
    problem.addConstraint(lambda f1, c1: (f1 == "roses") == (c1 == "red"), ["flower1", "color1"])
    problem.addConstraint(lambda f2, c2: (f2 == "roses") == (c2 == "red"), ["flower2", "color2"])
    problem.addConstraint(lambda f3, c3: (f3 == "roses") == (c3 == "red"), ["flower3", "color3"])
    problem.addConstraint(lambda f4, c4: (f4 == "roses") == (c4 == "red"), ["flower4", "color4"])
    
    # Clue 6: The person in a Craftsman-style house is in the second house.
    problem.addConstraint(lambda s2: s2 == "craftsman", ["style2"])
    
    # Clue 7: Eric is the person residing in a Victorian house.
    problem.addConstraint(lambda n1, s1: (n1 == "Eric") == (s1 == "victorian"), ["name1", "style1"])
    problem.addConstraint(lambda n2, s2: (n2 == "Eric") == (s2 == "victorian"), ["name2", "style2"])
    problem.addConstraint(lambda n3, s3: (n3 == "Eric") == (s3 == "victorian"), ["name3", "style3"])
    problem.addConstraint(lambda n4, s4: (n4 == "Eric") == (s4 == "victorian"), ["name4", "style4"])
    
    # Clue 8: The person with an aquarium of fish is the person who loves white.
    problem.addConstraint(lambda p1, c1: (p1 == "fish") == (c1 == "white"), ["pet1", "color1"])
    problem.addConstraint(lambda p2, c2: (p2 == "fish") == (c2 == "white"), ["pet2", "color2"])
    problem.addConstraint(lambda p3, c3: (p3 == "fish") == (c3 == "white"), ["pet3", "color3"])
    problem.addConstraint(lambda p4, c4: (p4 == "fish") == (c4 == "white"), ["pet4", "color4"])
    
    # Clue 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
    def cooking_right_of_red(h1, h2, h3, h4, c1, c2, c3, c4):
        red_house = None
        cooking_house = None
        if c1 == "red": red_house = 1
        if c2 == "red": red_house = 2
        if c3 == "red": red_house = 3
        if c4 == "red": red_house = 4
        if h1 == "cooking": cooking_house = 1
        if h2 == "cooking": cooking_house = 2
        if h3 == "cooking": cooking_house = 3
        if h4 == "cooking": cooking_house = 4
        return cooking_house > red_house
    
    problem.addConstraint(cooking_right_of_red, 
                         ["hobby1", "hobby2", "hobby3", "hobby4", "color1", "color2", "color3", "color4"])
    
    # Clue 10: The person who loves white is the person who loves a carnations arrangement.
    problem.addConstraint(lambda c1, f1: (c1 == "white") == (f1 == "carnations"), ["color1", "flower1"])
    problem.addConstraint(lambda c2, f2: (c2 == "white") == (f2 == "carnations"), ["color2", "flower2"])
    problem.addConstraint(lambda c3, f3: (c3 == "white") == (f3 == "carnations"), ["color3", "flower3"])
    problem.addConstraint(lambda c4, f4: (c4 == "white") == (f4 == "carnations"), ["color4", "flower4"])
    
    # Clue 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
    def white_right_of_gardening(c1, c2, c3, c4, h1, h2, h3, h4):
        gardening_house = None
        white_house = None
        if h1 == "gardening": gardening_house = 1
        if h2 == "gardening": gardening_house = 2
        if h3 == "gardening": gardening_house = 3
        if h4 == "gardening": gardening_house = 4
        if c1 == "white": white_house = 1
        if c2 == "white": white_house = 2
        if c3 == "white": white_house = 3
        if c4 == "white": white_house = 4
        return white_house > gardening_house
    
    problem.addConstraint(white_right_of_gardening, 
                         ["color1", "color2", "color3", "color4", "hobby1", "hobby2", "hobby3", "hobby4"])
    
    # Clue 12: The person who loves a bouquet of daffodils is the person who loves yellow.
    problem.addConstraint(lambda f1, c1: (f1 == "daffodils") == (c1 == "yellow"), ["flower1", "color1"])
    problem.addConstraint(lambda f2, c2: (f2 == "daffodils") == (c2 == "yellow"), ["flower2", "color2"])
    problem.addConstraint(lambda f3, c3: (f3 == "daffodils") == (c3 == "yellow"), ["flower3", "color3"])
    problem.addConstraint(lambda f4, c4: (f4 == "daffodils") == (c4 == "yellow"), ["flower4", "color4"])
    
    # Clue 13: The person living in a colonial-style house is the person whose favorite color is red.
    problem.addConstraint(lambda s1, c1: (s1 == "colonial") == (c1 == "red"), ["style1", "color1"])
    problem.addConstraint(lambda s2, c2: (s2 == "colonial") == (c2 == "red"), ["style2", "color2"])
    problem.addConstraint(lambda s3, c3: (s3 == "colonial") == (c3 == "red"), ["style3", "color3"])
    problem.addConstraint(lambda s4, c4: (s4 == "colonial") == (c4 == "red"), ["style4", "color4"])
    
    # Clue 14: The person who has a cat is Eric.
    problem.addConstraint(lambda p1, n1: (p1 == "cat") == (n1 == "Eric"), ["pet1", "name1"])
    problem.addConstraint(lambda p2, n2: (p2 == "cat") == (n2 == "Eric"), ["pet2", "name2"])
    problem.addConstraint(lambda p3, n3: (p3 == "cat") == (n3 == "Eric"), ["pet3", "name3"])
    problem.addConstraint(lambda p4, n4: (p4 == "cat") == (n4 == "Eric"), ["pet4", "name4"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the output structure
    header = ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f"name{house}"],
            solution[f"flower{house}"],
            solution[f"hobby{house}"],
            solution[f"pet{house}"],
            solution[f"color{house}"],
            solution[f"style{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))