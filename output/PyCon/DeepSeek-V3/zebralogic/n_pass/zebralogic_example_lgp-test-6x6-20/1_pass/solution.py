import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-6)
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define all possible values for each category
    names = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
    cigars = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
    music_genres = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
    drinks = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
    mothers = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
    foods = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]
    
    # Add variables for each category
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"cigar_{house}", cigars)
        problem.addVariable(f"music_{house}", music_genres)
        problem.addVariable(f"drink_{house}", drinks)
        problem.addVariable(f"mother_{house}", mothers)
        problem.addVariable(f"food_{house}", foods)
    
    # All attributes must be unique within their categories
    for attr in ["name", "cigar", "music", "drink", "mother", "food"]:
        problem.addConstraint(AllDifferentConstraint(), [f"{attr}_{house}" for house in houses])
    
    # Clue 1: Carol is directly left of the person who loves eating grilled cheese.
    for i in range(1, 6):
        problem.addConstraint(
            lambda carol, grilled: carol == "Carol" and grilled == "grilled cheese",
            [f"name_{i}", f"food_{i+1}"]
        )
    
    # Clue 2: Eric is not in the second house.
    problem.addConstraint(lambda x: x != "Eric", ["name_2"])
    
    # Clue 3: The person whose mother's name is Holly is somewhere to the right of Carol.
    def holly_right_of_carol(*args):
        carol_pos = None
        holly_pos = None
        for i, (name, mother) in enumerate(args):
            if name == "Carol":
                carol_pos = i
            if mother == "Holly":
                holly_pos = i
        return carol_pos is not None and holly_pos is not None and holly_pos > carol_pos
    
    problem.addConstraint(holly_right_of_carol, 
                         [(f"name_{house}", f"mother_{house}") for house in houses])
    
    # Clue 4: The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
    def grilled_right_of_rock(*args):
        rock_pos = None
        grilled_pos = None
        for i, (music, food) in enumerate(args):
            if music == "rock":
                rock_pos = i
            if food == "grilled cheese":
                grilled_pos = i
        return rock_pos is not None and grilled_pos is not None and grilled_pos > rock_pos
    
    problem.addConstraint(grilled_right_of_rock, 
                         [(f"music_{house}", f"food_{house}") for house in houses])
    
    # Clue 5: Eric is directly left of Carol.
    for i in range(1, 6):
        problem.addConstraint(
            lambda eric, carol: eric == "Eric" and carol == "Carol",
            [f"name_{i}", f"name_{i+1}"]
        )
    
    # Clue 6: The person who loves pop music is not in the third house.
    problem.addConstraint(lambda x: x != "pop", ["music_3"])
    
    # Clue 7: Eric is the person who loves country music.
    for house in houses:
        problem.addConstraint(
            lambda name, music: not (name == "Eric" and music != "country") and not (music == "country" and name != "Eric"),
            [f"name_{house}", f"music_{house}"]
        )
    
    # Clue 8: The person who loves classical music is in the sixth house.
    problem.addConstraint(lambda x: x == "classical", ["music_6"])
    
    # Clue 9: The coffee drinker is Bob.
    for house in houses:
        problem.addConstraint(
            lambda name, drink: not (name == "Bob" and drink != "coffee") and not (drink == "coffee" and name != "Bob"),
            [f"name_{house}", f"drink_{house}"]
        )
    
    # Clue 10: The person who smokes many unique blends is Peter.
    for house in houses:
        problem.addConstraint(
            lambda name, cigar: not (name == "Peter" and cigar != "blends") and not (cigar == "blends" and name != "Peter"),
            [f"name_{house}", f"cigar_{house}"]
        )
    
    # Clue 11: The person who loves the stew is not in the fifth house.
    problem.addConstraint(lambda x: x != "stew", ["food_5"])
    
    # Clue 12: The root beer lover is directly left of The person whose mother's name is Janelle.
    for i in range(1, 6):
        problem.addConstraint(
            lambda drink, mother: drink == "root beer" and mother == "Janelle",
            [f"drink_{i}", f"mother_{i+1}"]
        )
    
    # Clue 13: There are two houses between The person whose mother's name is Sarah and the person who smokes Yellow Monster.
    def two_houses_between(*args):
        sarah_pos = None
        yellow_monster_pos = None
        for i, (mother, cigar) in enumerate(args):
            if mother == "Sarah":
                sarah_pos = i
            if cigar == "yellow monster":
                yellow_monster_pos = i
        return (sarah_pos is not None and yellow_monster_pos is not None and 
                abs(sarah_pos - yellow_monster_pos) == 3)
    
    problem.addConstraint(two_houses_between, 
                         [(f"mother_{house}", f"cigar_{house}") for house in houses])
    
    # Clue 14: Eric is the tea drinker.
    for house in houses:
        problem.addConstraint(
            lambda name, drink: not (name == "Eric" and drink != "tea") and not (drink == "tea" and name != "Eric"),
            [f"name_{house}", f"drink_{house}"]
        )
    
    # Clue 15: The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
    def pallmall_right_of_stirfry(*args):
        stirfry_pos = None
        pallmall_pos = None
        for i, (food, cigar) in enumerate(args):
            if food == "stir fry":
                stirfry_pos = i
            if cigar == "pall mall":
                pallmall_pos = i
        return stirfry_pos is not None and pallmall_pos is not None and pallmall_pos > stirfry_pos
    
    problem.addConstraint(pallmall_right_of_stirfry, 
                         [(f"food_{house}", f"cigar_{house}") for house in houses])
    
    # Clue 16: The person who loves the soup is Bob.
    for house in houses:
        problem.addConstraint(
            lambda name, food: not (name == "Bob" and food != "soup") and not (food == "soup" and name != "Bob"),
            [f"name_{house}", f"food_{house}"]
        )
    
    # Clue 17: The person who loves hip-hop music is directly left of The person whose mother's name is Kailyn.
    for i in range(1, 6):
        problem.addConstraint(
            lambda music, mother: music == "hip hop" and mother == "Kailyn",
            [f"music_{i}", f"mother_{i+1}"]
        )
    
    # Clue 18: Arnold is somewhere to the right of The person whose mother's name is Kailyn.
    def arnold_right_of_kailyn(*args):
        kailyn_pos = None
        arnold_pos = None
        for i, (mother, name) in enumerate(args):
            if mother == "Kailyn":
                kailyn_pos = i
            if name == "Arnold":
                arnold_pos = i
        return kailyn_pos is not None and arnold_pos is not None and arnold_pos > kailyn_pos
    
    problem.addConstraint(arnold_right_of_kailyn, 
                         [(f"mother_{house}", f"name_{house}") for house in houses])
    
    # Clue 19: The one who only drinks water is directly left of the person who smokes Blue Master.
    for i in range(1, 6):
        problem.addConstraint(
            lambda drink, cigar: drink == "water" and cigar == "blue master",
            [f"drink_{i}", f"cigar_{i+1}"]
        )
    
    # Clue 20: The person who loves the spaghetti eater is somewhere to the left of the person who smokes many unique blends.
    def spaghetti_left_of_blends(*args):
        spaghetti_pos = None
        blends_pos = None
        for i, (food, cigar) in enumerate(args):
            if food == "spaghetti":
                spaghetti_pos = i
            if cigar == "blends":
                blends_pos = i
        return spaghetti_pos is not None and blends_pos is not None and spaghetti_pos < blends_pos
    
    problem.addConstraint(spaghetti_left_of_blends, 
                         [(f"food_{house}", f"cigar_{house}") for house in houses])
    
    # Clue 21: The person whose mother's name is Sarah is directly left of the person who loves jazz music.
    for i in range(1, 6):
        problem.addConstraint(
            lambda mother, music: mother == "Sarah" and music == "jazz",
            [f"mother_{i}", f"music_{i+1}"]
        )
    
    # Clue 22: The person who loves hip-hop music is directly left of the root beer lover.
    for i in range(1, 6):
        problem.addConstraint(
            lambda music, drink: music == "hip hop" and drink == "root beer",
            [f"music_{i}", f"drink_{i+1}"]
        )
    
    # Clue 23: The one who only drinks water is the person who loves the stew.
    for house in houses:
        problem.addConstraint(
            lambda drink, food: not (drink == "water" and food != "stew") and not (food == "stew" and drink != "water"),
            [f"drink_{house}", f"food_{house}"]
        )
    
    # Clue 24: The Dunhill smoker is not in the second house.
    problem.addConstraint(lambda x: x != "dunhill", ["cigar_2"])
    
    # Clue 25: The person who likes milk is The person whose mother's name is Janelle.
    for house in houses:
        problem.addConstraint(
            lambda drink, mother: not (drink == "milk" and mother != "Janelle") and not (mother == "Janelle" and drink != "milk"),
            [f"drink_{house}", f"mother_{house}"]
        )
    
    # Clue 26: Eric is The person whose mother's name is Aniya.
    for house in houses:
        problem.addConstraint(
            lambda name, mother: not (name == "Eric" and mother != "Aniya") and not (mother == "Aniya" and name != "Eric"),
            [f"name_{house}", f"mother_{house}"]
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Format the solution
    header = ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"cigar_{house}"],
            solution[f"music_{house}"],
            solution[f"drink_{house}"],
            solution[f"mother_{house}"],
            solution[f"food_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))