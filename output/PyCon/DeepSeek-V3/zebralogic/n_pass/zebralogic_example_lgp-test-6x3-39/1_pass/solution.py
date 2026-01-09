import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables: houses 1 to 6
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define domains for each attribute
    names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]
    
    # Add variables for each house
    problem.addVariables(["name"] + houses, names)
    problem.addVariables(["child"] + houses, children)
    problem.addVariables(["smoothie"] + houses, smoothies)
    
    # All attributes must be unique
    problem.addConstraint(AllDifferentConstraint(), ["name"] + houses)
    problem.addConstraint(AllDifferentConstraint(), ["child"] + houses)
    problem.addConstraint(AllDifferentConstraint(), ["smoothie"] + houses)
    
    # Clue 1: Fred child and Desert smoothie lover are next to each other
    def adjacent_fred_desert(*args):
        fred_house = None
        desert_house = None
        for i in range(1, 7):
            if args[i-1] == "Fred":  # child at position i
                fred_house = i
            if args[i+5] == "desert":  # smoothie at position i
                desert_house = i
        return abs(fred_house - desert_house) == 1
    
    problem.addConstraint(adjacent_fred_desert, 
                         ["child1", "child2", "child3", "child4", "child5", "child6",
                          "smoothie1", "smoothie2", "smoothie3", "smoothie4", "smoothie5", "smoothie6"])
    
    # Clue 2: Blueberry smoothie is left of Fred child
    def blueberry_left_of_fred(*args):
        blueberry_house = None
        fred_house = None
        for i in range(1, 7):
            if args[i-1] == "Fred":  # child at position i
                fred_house = i
            if args[i+5] == "blueberry":  # smoothie at position i
                blueberry_house = i
        return blueberry_house < fred_house
    
    problem.addConstraint(blueberry_left_of_fred,
                         ["child1", "child2", "child3", "child4", "child5", "child6",
                          "smoothie1", "smoothie2", "smoothie3", "smoothie4", "smoothie5", "smoothie6"])
    
    # Clue 3: Alice is not in fifth house
    problem.addConstraint(lambda name5: name5 != "Alice", ["name5"])
    
    # Clue 4: Samantha child is not in second house
    problem.addConstraint(lambda child2: child2 != "Samantha", ["child2"])
    
    # Clue 5: Watermelon smoothie is right of Cherry smoothie
    def watermelon_right_of_cherry(*args):
        cherry_house = None
        watermelon_house = None
        for i in range(1, 7):
            if args[i-1] == "cherry":  # smoothie at position i
                cherry_house = i
            if args[i-1] == "watermelon":  # smoothie at position i
                watermelon_house = i
        return watermelon_house > cherry_house
    
    problem.addConstraint(watermelon_right_of_cherry,
                         ["smoothie1", "smoothie2", "smoothie3", "smoothie4", "smoothie5", "smoothie6"])
    
    # Clue 6: Alice is the child of Alice
    def alice_child_of_alice(*args):
        for i in range(1, 7):
            if args[i-1] == "Alice":  # name at position i
                if args[i+5] != "Alice":  # child at position i
                    return False
            if args[i+5] == "Alice":  # child at position i
                if args[i-1] != "Alice":  # name at position i
                    return False
        return True
    
    problem.addConstraint(alice_child_of_alice,
                         ["name1", "name2", "name3", "name4", "name5", "name6",
                          "child1", "child2", "child3", "child4", "child5", "child6"])
    
    # Clue 7: Alice is the Watermelon smoothie lover
    def alice_watermelon(*args):
        for i in range(1, 7):
            if args[i-1] == "Alice":  # name at position i
                if args[i+5] != "watermelon":  # smoothie at position i
                    return False
            if args[i+5] == "watermelon":  # smoothie at position i
                if args[i-1] != "Alice":  # name at position i
                    return False
        return True
    
    problem.addConstraint(alice_watermelon,
                         ["name1", "name2", "name3", "name4", "name5", "name6",
                          "smoothie1", "smoothie2", "smoothie3", "smoothie4", "smoothie5", "smoothie6"])
    
    # Clue 8: Peter is right of Samantha child
    def peter_right_of_samantha(*args):
        peter_house = None
        samantha_house = None
        for i in range(1, 7):
            if args[i-1] == "Samantha":  # child at position i
                samantha_house = i
            if args[i+5] == "Peter":  # name at position i
                peter_house = i
        return peter_house > samantha_house
    
    problem.addConstraint(peter_right_of_samantha,
                         ["child1", "child2", "child3", "child4", "child5", "child6",
                          "name1", "name2", "name3", "name4", "name5", "name6"])
    
    # Clue 9: Arnold is not in second house
    problem.addConstraint(lambda name2: name2 != "Arnold", ["name2"])
    
    # Clue 10: Bob is mother of Timothy
    def bob_timothy(*args):
        for i in range(1, 7):
            if args[i-1] == "Bob":  # name at position i
                if args[i+5] != "Timothy":  # child at position i
                    return False
            if args[i+5] == "Timothy":  # child at position i
                if args[i-1] != "Bob":  # name at position i
                    return False
        return True
    
    problem.addConstraint(bob_timothy,
                         ["name1", "name2", "name3", "name4", "name5", "name6",
                          "child1", "child2", "child3", "child4", "child5", "child6"])
    
    # Clue 11: Arnold is directly left of Carol
    def arnold_left_carol(*args):
        for i in range(1, 6):  # Check houses 1-5
            if args[i-1] == "Arnold" and args[i] == "Carol":
                return True
        return False
    
    problem.addConstraint(arnold_left_carol, ["name1", "name2", "name3", "name4", "name5", "name6"])
    
    # Clue 12: Cherry smoothie is directly left of Samantha child
    def cherry_left_samantha(*args):
        for i in range(1, 6):  # Check houses 1-5
            if args[i-1] == "cherry" and args[i] == "Samantha":
                return True
        return False
    
    problem.addConstraint(cherry_left_samantha, ["smoothie1", "smoothie2", "smoothie3", "smoothie4", "smoothie5", "smoothie6",
                                                "child1", "child2", "child3", "child4", "child5", "child6"])
    
    # Clue 13: Meredith child is in sixth house
    problem.addConstraint(lambda child6: child6 == "Meredith", ["child6"])
    
    # Clue 14: Dragonfruit smoothie lover is Meredith child
    def dragonfruit_meredith(*args):
        for i in range(1, 7):
            if args[i-1] == "Meredith":  # child at position i
                if args[i+5] != "dragonfruit":  # smoothie at position i
                    return False
            if args[i+5] == "dragonfruit":  # smoothie at position i
                if args[i-1] != "Meredith":  # child at position i
                    return False
        return True
    
    problem.addConstraint(dragonfruit_meredith,
                         ["child1", "child2", "child3", "child4", "child5", "child6",
                          "smoothie1", "smoothie2", "smoothie3", "smoothie4", "smoothie5", "smoothie6"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Children", "Smoothie"], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in range(1, 7):
        name = solution[f"name{house}"]
        child = solution[f"child{house}"]
        smoothie = solution[f"smoothie{house}"]
        rows.append([str(house), name, child, smoothie])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Children", "Smoothie"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))