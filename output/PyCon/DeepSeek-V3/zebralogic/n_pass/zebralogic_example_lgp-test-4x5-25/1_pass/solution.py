import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-4)
    houses = [1, 2, 3, 4]
    
    # Define domains for each attribute
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["craftsman", "colonial", "victorian", "ranch"]
    hair_colors = ["red", "blonde", "black", "brown"]
    children = ["Bella", "Fred", "Meredith", "Samantha"]
    genres = ["mystery", "fantasy", "romance", "science fiction"]
    
    # Add variables for each attribute
    problem.addVariable("name", names)
    problem.addVariable("style", styles)
    problem.addVariable("hair", hair_colors)
    problem.addVariable("child", children)
    problem.addVariable("genre", genres)
    
    # All attributes must be different
    problem.addConstraint(lambda n1, n2, n3, n4: len({n1, n2, n3, n4}) == 4, ["name", "name", "name", "name"])
    problem.addConstraint(lambda s1, s2, s3, s4: len({s1, s2, s3, s4}) == 4, ["style", "style", "style", "style"])
    problem.addConstraint(lambda h1, h2, h3, h4: len({h1, h2, h3, h4}) == 4, ["hair", "hair", "hair", "hair"])
    problem.addConstraint(lambda c1, c2, c3, c4: len({c1, c2, c3, c4}) == 4, ["child", "child", "child", "child"])
    problem.addConstraint(lambda g1, g2, g3, g4: len({g1, g2, g3, g4}) == 4, ["genre", "genre", "genre", "genre"])
    
    # Clue 1: The person in a Craftsman-style house is in the third house.
    problem.addConstraint(lambda style: style == "craftsman", ["style_3"])
    
    # Clue 2: Alice is the person who loves romance books.
    problem.addConstraint(lambda name, genre: name == "Alice" and genre == "romance", ["name_Alice", "genre_Alice"])
    
    # Clue 3: The person who has brown hair is in the fourth house.
    problem.addConstraint(lambda hair: hair == "brown", ["hair_4"])
    
    # Clue 4: The person's child is named Samantha is in the fourth house.
    problem.addConstraint(lambda child: child == "Samantha", ["child_4"])
    
    # Clue 5: The person in a ranch-style home is somewhere to the right of the person who has red hair.
    def ranch_right_of_red(style1, style2, style3, style4, hair1, hair2, hair3, hair4):
        red_house = None
        ranch_house = None
        for i, (s, h) in enumerate([(style1, hair1), (style2, hair2), (style3, hair3), (style4, hair4)], 1):
            if h == "red":
                red_house = i
            if s == "ranch":
                ranch_house = i
        return ranch_house > red_house
    
    problem.addConstraint(ranch_right_of_red, 
                         ["style_1", "style_2", "style_3", "style_4", 
                          "hair_1", "hair_2", "hair_3", "hair_4"])
    
    # Clue 6: Peter is the person's child is named Bella.
    problem.addConstraint(lambda name, child: name == "Peter" and child == "Bella", ["name_Peter", "child_Peter"])
    
    # Clue 7: Arnold is the person who has red hair.
    problem.addConstraint(lambda name, hair: name == "Arnold" and hair == "red", ["name_Arnold", "hair_Arnold"])
    
    # Clue 8: Alice is the person living in a colonial-style house.
    problem.addConstraint(lambda name, style: name == "Alice" and style == "colonial", ["name_Alice", "style_Alice"])
    
    # Clue 9: The person who has black hair is in the second house.
    problem.addConstraint(lambda hair: hair == "black", ["hair_2"])
    
    # Clue 10: The person who loves fantasy books is Peter.
    problem.addConstraint(lambda name, genre: name == "Peter" and genre == "fantasy", ["name_Peter", "genre_Peter"])
    
    # Clue 11: Arnold is the person's child is named Meredith.
    problem.addConstraint(lambda name, child: name == "Arnold" and child == "Meredith", ["name_Arnold", "child_Arnold"])
    
    # Clue 12: The person who has black hair is Eric.
    problem.addConstraint(lambda name, hair: name == "Eric" and hair == "black", ["name_Eric", "hair_Eric"])
    
    # Clue 13: The person who loves science fiction books is Arnold.
    problem.addConstraint(lambda name, genre: name == "Arnold" and genre == "science fiction", ["name_Arnold", "genre_Arnold"])
    
    # Create individual variables for each house
    variables = {}
    for house in houses:
        for attr in ["name", "style", "hair", "child", "genre"]:
            var_name = f"{attr}_{house}"
            problem.addVariable(var_name, 
                               names if attr == "name" else
                               styles if attr == "style" else
                               hair_colors if attr == "hair" else
                               children if attr == "child" else
                               genres)
            variables[(attr, house)] = var_name
    
    # Link individual variables to the main variables
    for house in houses:
        problem.addConstraint(lambda n, n_h=n: n == n_h, 
                            [f"name_{house}", "name"])
        problem.addConstraint(lambda s, s_h=s: s == s_h, 
                            [f"style_{house}", "style"])
        problem.addConstraint(lambda h, h_h=h: h == h_h, 
                            [f"hair_{house}", "hair"])
        problem.addConstraint(lambda c, c_h=c: c == c_h, 
                            [f"child_{house}", "child"])
        problem.addConstraint(lambda g, g_h=g: g == g_h, 
                            [f"genre_{house}", "genre"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"style_{house}"],
            solution[f"hair_{house}"],
            solution[f"child_{house}"],
            solution[f"genre_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))