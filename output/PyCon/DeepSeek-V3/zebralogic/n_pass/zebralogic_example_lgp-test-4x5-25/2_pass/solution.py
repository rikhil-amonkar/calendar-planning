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
    
    # Create individual variables for each house and each attribute
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"style_{house}", styles)
        problem.addVariable(f"hair_{house}", hair_colors)
        problem.addVariable(f"child_{house}", children)
        problem.addVariable(f"genre_{house}", genres)
    
    # All attributes must be different within each category
    problem.addConstraint(lambda n1, n2, n3, n4: len({n1, n2, n3, n4}) == 4, 
                         [f"name_{i}" for i in houses])
    problem.addConstraint(lambda s1, s2, s3, s4: len({s1, s2, s3, s4}) == 4, 
                         [f"style_{i}" for i in houses])
    problem.addConstraint(lambda h1, h2, h3, h4: len({h1, h2, h3, h4}) == 4, 
                         [f"hair_{i}" for i in houses])
    problem.addConstraint(lambda c1, c2, c3, c4: len({c1, c2, c3, c4}) == 4, 
                         [f"child_{i}" for i in houses])
    problem.addConstraint(lambda g1, g2, g3, g4: len({g1, g2, g3, g4}) == 4, 
                         [f"genre_{i}" for i in houses])
    
    # Clue 1: The person in a Craftsman-style house is in the third house.
    problem.addConstraint(lambda style_3: style_3 == "craftsman", ["style_3"])
    
    # Clue 2: Alice is the person who loves romance books.
    # We need to find which house has Alice and ensure that house has romance genre
    def alice_romance(name1, name2, name3, name4, genre1, genre2, genre3, genre4):
        for i, (n, g) in enumerate([(name1, genre1), (name2, genre2), (name3, genre3), (name4, genre4)], 1):
            if n == "Alice":
                return g == "romance"
        return False
    problem.addConstraint(alice_romance, 
                         [f"name_{i}" for i in houses] + [f"genre_{i}" for i in houses])
    
    # Clue 3: The person who has brown hair is in the fourth house.
    problem.addConstraint(lambda hair_4: hair_4 == "brown", ["hair_4"])
    
    # Clue 4: The person's child is named Samantha is in the fourth house.
    problem.addConstraint(lambda child_4: child_4 == "Samantha", ["child_4"])
    
    # Clue 5: The person in a ranch-style home is somewhere to the right of the person who has red hair.
    def ranch_right_of_red(style1, style2, style3, style4, hair1, hair2, hair3, hair4):
        red_house = None
        ranch_house = None
        for i, (s, h) in enumerate([(style1, hair1), (style2, hair2), (style3, hair3), (style4, hair4)], 1):
            if h == "red":
                red_house = i
            if s == "ranch":
                ranch_house = i
        return ranch_house is not None and red_house is not None and ranch_house > red_house
    
    problem.addConstraint(ranch_right_of_red, 
                         [f"style_{i}" for i in houses] + [f"hair_{i}" for i in houses])
    
    # Clue 6: Peter is the person's child is named Bella.
    def peter_bella(name1, name2, name3, name4, child1, child2, child3, child4):
        for i, (n, c) in enumerate([(name1, child1), (name2, child2), (name3, child3), (name4, child4)], 1):
            if n == "Peter":
                return c == "Bella"
        return False
    problem.addConstraint(peter_bella, 
                         [f"name_{i}" for i in houses] + [f"child_{i}" for i in houses])
    
    # Clue 7: Arnold is the person who has red hair.
    def arnold_red(name1, name2, name3, name4, hair1, hair2, hair3, hair4):
        for i, (n, h) in enumerate([(name1, hair1), (name2, hair2), (name3, hair3), (name4, hair4)], 1):
            if n == "Arnold":
                return h == "red"
        return False
    problem.addConstraint(arnold_red, 
                         [f"name_{i}" for i in houses] + [f"hair_{i}" for i in houses])
    
    # Clue 8: Alice is the person living in a colonial-style house.
    def alice_colonial(name1, name2, name3, name4, style1, style2, style3, style4):
        for i, (n, s) in enumerate([(name1, style1), (name2, style2), (name3, style3), (name4, style4)], 1):
            if n == "Alice":
                return s == "colonial"
        return False
    problem.addConstraint(alice_colonial, 
                         [f"name_{i}" for i in houses] + [f"style_{i}" for i in houses])
    
    # Clue 9: The person who has black hair is in the second house.
    problem.addConstraint(lambda hair_2: hair_2 == "black", ["hair_2"])
    
    # Clue 10: The person who loves fantasy books is Peter.
    def peter_fantasy(name1, name2, name3, name4, genre1, genre2, genre3, genre4):
        for i, (n, g) in enumerate([(name1, genre1), (name2, genre2), (name3, genre3), (name4, genre4)], 1):
            if n == "Peter":
                return g == "fantasy"
        return False
    problem.addConstraint(peter_fantasy, 
                         [f"name_{i}" for i in houses] + [f"genre_{i}" for i in houses])
    
    # Clue 11: Arnold is the person's child is named Meredith.
    def arnold_meredith(name1, name2, name3, name4, child1, child2, child3, child4):
        for i, (n, c) in enumerate([(name1, child1), (name2, child2), (name3, child3), (name4, child4)], 1):
            if n == "Arnold":
                return c == "Meredith"
        return False
    problem.addConstraint(arnold_meredith, 
                         [f"name_{i}" for i in houses] + [f"child_{i}" for i in houses])
    
    # Clue 12: The person who has black hair is Eric.
    def eric_black(name1, name2, name3, name4, hair1, hair2, hair3, hair4):
        for i, (n, h) in enumerate([(name1, hair1), (name2, hair2), (name3, hair3), (name4, hair4)], 1):
            if n == "Eric":
                return h == "black"
        return False
    problem.addConstraint(eric_black, 
                         [f"name_{i}" for i in houses] + [f"hair_{i}" for i in houses])
    
    # Clue 13: The person who loves science fiction books is Arnold.
    def arnold_scifi(name1, name2, name3, name4, genre1, genre2, genre3, genre4):
        for i, (n, g) in enumerate([(name1, genre1), (name2, genre2), (name3, genre3), (name4, genre4)], 1):
            if n == "Arnold":
                return g == "science fiction"
        return False
    problem.addConstraint(arnold_scifi, 
                         [f"name_{i}" for i in houses] + [f"genre_{i}" for i in houses])
    
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