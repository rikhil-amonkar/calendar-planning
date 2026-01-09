import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-4)
    houses = [1, 2, 3, 4]
    
    # Define domains for each attribute
    names = ["Peter", "Alice", "Eric", "Arnold"]
    mothers = ["Janelle", "Holly", "Aniya", "Kailyn"]
    smoothies = ["watermelon", "dragonfruit", "desert", "cherry"]
    heights = ["tall", "average", "short", "very short"]
    educations = ["high school", "associate", "master", "bachelor"]
    
    # Add variables for each attribute per house
    problem.addVariables(["name1", "name2", "name3", "name4"], names)
    problem.addVariables(["mother1", "mother2", "mother3", "mother4"], mothers)
    problem.addVariables(["smoothie1", "smoothie2", "smoothie3", "smoothie4"], smoothies)
    problem.addVariables(["height1", "height2", "height3", "height4"], heights)
    problem.addVariables(["education1", "education2", "education3", "education4"], educations)
    
    # All attributes must be different within their category
    problem.addConstraint(AllDifferentConstraint(), ["name1", "name2", "name3", "name4"])
    problem.addConstraint(AllDifferentConstraint(), ["mother1", "mother2", "mother3", "mother4"])
    problem.addConstraint(AllDifferentConstraint(), ["smoothie1", "smoothie2", "smoothie3", "smoothie4"])
    problem.addConstraint(AllDifferentConstraint(), ["height1", "height2", "height3", "height4"])
    problem.addConstraint(AllDifferentConstraint(), ["education1", "education2", "education3", "education4"])
    
    # Clue 1: The person whose mother's name is Janelle is in the third house.
    problem.addConstraint(lambda mother3: mother3 == "Janelle", ["mother3"])
    
    # Clue 2: The Desert smoothie lover is the person with a master's degree.
    for i in houses:
        problem.addConstraint(
            lambda smoothie, education, house=i: not (smoothie == "desert" and education != "master") and
                                                 not (education == "master" and smoothie != "desert"),
            [f"smoothie{i}", f"education{i}"]
        )
    
    # Clue 3: The Desert smoothie lover is not in the first house.
    problem.addConstraint(lambda smoothie1: smoothie1 != "desert", ["smoothie1"])
    
    # Clue 4: The person who is very short is somewhere to the left of the person with a high school diploma.
    def left_of_very_short_high_school(*args):
        very_short_pos = None
        high_school_pos = None
        for i, height in enumerate(args[:4]):
            if height == "very short":
                very_short_pos = i + 1
        for i, education in enumerate(args[4:]):
            if education == "high school":
                high_school_pos = i + 1
        return very_short_pos is not None and high_school_pos is not None and very_short_pos < high_school_pos
    
    problem.addConstraint(left_of_very_short_high_school, 
                         ["height1", "height2", "height3", "height4",
                          "education1", "education2", "education3", "education4"])
    
    # Clue 5: Eric and the person who likes Cherry smoothies are next to each other.
    def eric_next_to_cherry(*args):
        eric_pos = None
        cherry_pos = None
        for i, name in enumerate(args[:4]):
            if name == "Eric":
                eric_pos = i + 1
        for i, smoothie in enumerate(args[4:]):
            if smoothie == "cherry":
                cherry_pos = i + 1
        return eric_pos is not None and cherry_pos is not None and abs(eric_pos - cherry_pos) == 1
    
    problem.addConstraint(eric_next_to_cherry, 
                         ["name1", "name2", "name3", "name4",
                          "smoothie1", "smoothie2", "smoothie3", "smoothie4"])
    
    # Clue 6: The person with a high school diploma is not in the third house.
    problem.addConstraint(lambda education3: education3 != "high school", ["education3"])
    
    # Clue 7: The person whose mother's name is Kailyn is the person with an associate's degree.
    for i in houses:
        problem.addConstraint(
            lambda mother, education, house=i: not (mother == "Kailyn" and education != "associate") and
                                              not (education == "associate" and mother != "Kailyn"),
            [f"mother{i}", f"education{i}"]
        )
    
    # Clue 8: The person who likes Cherry smoothies is The person whose mother's name is Aniya.
    for i in houses:
        problem.addConstraint(
            lambda smoothie, mother, house=i: not (smoothie == "cherry" and mother != "Aniya") and
                                             not (mother == "Aniya" and smoothie != "cherry"),
            [f"smoothie{i}", f"mother{i}"]
        )
    
    # Clue 9: The person who is tall is The person whose mother's name is Janelle.
    for i in houses:
        problem.addConstraint(
            lambda height, mother, house=i: not (height == "tall" and mother != "Janelle") and
                                           not (mother == "Janelle" and height != "tall"),
            [f"height{i}", f"mother{i}"]
        )
    
    # Clue 10: Arnold is somewhere to the right of the person who has an average height.
    def arnold_right_of_average(*args):
        arnold_pos = None
        average_pos = None
        for i, name in enumerate(args[:4]):
            if name == "Arnold":
                arnold_pos = i + 1
        for i, height in enumerate(args[4:]):
            if height == "average":
                average_pos = i + 1
        return arnold_pos is not None and average_pos is not None and arnold_pos > average_pos
    
    problem.addConstraint(arnold_right_of_average, 
                         ["name1", "name2", "name3", "name4",
                          "height1", "height2", "height3", "height4"])
    
    # Clue 11: The Dragonfruit smoothie lover is directly left of the person who is short.
    def dragonfruit_left_of_short(*args):
        dragonfruit_pos = None
        short_pos = None
        for i, smoothie in enumerate(args[:4]):
            if smoothie == "dragonfruit":
                dragonfruit_pos = i + 1
        for i, height in enumerate(args[4:]):
            if height == "short":
                short_pos = i + 1
        return dragonfruit_pos is not None and short_pos is not None and dragonfruit_pos + 1 == short_pos
    
    problem.addConstraint(dragonfruit_left_of_short, 
                         ["smoothie1", "smoothie2", "smoothie3", "smoothie4",
                          "height1", "height2", "height3", "height4"])
    
    # Clue 12: The person who is tall is Alice.
    for i in houses:
        problem.addConstraint(
            lambda height, name, house=i: not (height == "tall" and name != "Alice") and
                                         not (name == "Alice" and height != "tall"),
            [f"height{i}", f"name{i}"]
        )
    
    # Solve the puzzle
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Format the solution
    header = ["House", "Name", "Mother", "Smoothie", "Height", "Education"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f"name{house}"],
            solution[f"mother{house}"],
            solution[f"smoothie{house}"],
            solution[f"height{house}"],
            solution[f"education{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))