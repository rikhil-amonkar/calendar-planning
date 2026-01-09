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
            lambda name, food: name == "Carol" and food == "grilled cheese",
            [f"name_{i}", f"food_{i+1}"]
        )
    
    # Clue 2: Eric is not in the second house.
    problem.addConstraint(lambda x: x != "Eric", ["name_2"])
    
    # Clue 3: The person whose mother's name is Holly is somewhere to the right of Carol.
    def holly_right_of_carol(*args):
        # args will be: name_1, mother_1, name_2, mother_2, ..., name_6, mother_6
        carol_pos = None
        holly_pos = None
        for i in range(0, len(args), 2):
            name = args[i]
            mother = args[i+1]
            if name == "Carol":
                carol_pos = i // 2 + 1
            if mother == "Holly":
                holly_pos = i // 2 + 1
        return carol_pos is not None and holly_pos is not None and holly_pos > carol_pos
    
    # Create a flat list of variable names for this constraint
    var_list = []
    for house in houses:
        var_list.extend([f"name_{house}", f"mother_{house}"])
    problem.addConstraint(holly_right_of_carol, var_list)
    
    # Clue 4: The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
    def grilled_right_of_rock(*args):
        # args will be: music_1, food_1, music_2, food_2, ..., music_6, food_6
        rock_pos = None
        grilled_pos = None
        for i in range(0, len(args), 2):
            music = args[i]
            food = args[i+1]
            if music == "rock":
                rock_pos = i // 2 + 1
            if food == "grilled cheese":
                grilled_pos = i // 2 + 1
        return rock_pos is not None and grilled_pos is not None and grilled_pos > rock_pos
    
    var_list = []
    for house in houses:
        var_list.extend([f"music_{house}", f"food_{house}"])
    problem.addConstraint(grilled_right_of_rock, var_list)
    
    # Clue 5: Eric is directly left of Carol.
    for i in range(1, 6):
        problem.addConstraint(
            lambda name1, name2: name1 == "Eric" and name2 == "Carol",
            [f"name_{i}", f"name_{i+1}"]
        )
    
    # Clue 6: The person who loves pop music is not in the third house.
    problem.addConstraint(lambda x: x != "pop", ["music_3"])
    
    # Clue 7: Eric is the person who loves country music.
    for house in houses:
        problem.addConstraint(
            lambda name, music: (name == "Eric") == (music == "country"),
            [f"name_{house}", f"music_{house}"]
        )
    
    # Clue 8: The person who loves classical music is in the sixth house.
    problem.addConstraint(lambda x: x == "classical", ["music_6"])
    
    # Clue 9: The coffee drinker is Bob.
    for house in houses:
        problem.addConstraint(
            lambda name, drink: (name == "Bob") == (drink == "coffee"),
            [f"name_{house}", f"drink_{house}"]
        )
    
    # Clue 10: The person who smokes many unique blends is Peter.
    for house in houses:
        problem.addConstraint(
            lambda name, cigar: (name == "Peter") == (cigar == "blends"),
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
        # args will be: mother_1, cigar_1, mother_2, cigar_2, ..., mother_6, cigar_6
        sarah_pos = None
        yellow_monster_pos = None
        for i in range(0, len(args), 2):
            mother = args[i]
            cigar = args[i+1]
            if mother == "Sarah":
                sarah_pos = i // 2 + 1
            if cigar == "yellow monster":
                yellow_monster_pos = i // 2 + 1
        return (sarah_pos is not None and yellow_monster_pos is not None and 
                abs(sarah_pos - yellow_monster_pos) == 3)
    
    var_list = []
    for house in houses:
        var_list.extend([f"mother_{house}", f"cigar_{house}"])
    problem.addConstraint(two_houses_between, var_list)
    
    # Clue 14: Eric is the tea drinker.
    for house in houses:
        problem.addConstraint(
            lambda name, drink: (name == "Eric") == (drink == "tea"),
            [f"name_{house}", f"drink_{house}"]
        )
    
    # Clue 15: The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
    def pallmall_right_of_stirfry(*args):
        # args will be: food_1, cigar_1, food_2, cigar_2, ..., food_6, cigar_6
        stirfry_pos = None
        pallmall_pos = None
        for i in range(0, len(args), 2):
            food = args[i]
            cigar = args[i+1]
            if food == "stir fry":
                stirfry_pos = i // 2 + 1
            if cigar == "pall mall":
                pallmall_pos = i // 2 + 1
        return stirfry_pos is not None and pallmall_pos is not None and pallmall_pos > stirfry_pos
    
    var_list = []
    for house in houses:
        var_list.extend([f"food_{house}", f"cigar_{house}"])
    problem.addConstraint(pallmall_right_of_stirfry, var_list)
    
    # Clue 16: The person who loves the soup is Bob.
    for house in houses:
        problem.addConstraint(
            lambda name, food: (name == "Bob") == (food == "soup"),
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
        # args will be: mother_1, name_1, mother_2, name_2, ..., mother_6, name_6
        kailyn_pos = None
        arnold_pos = None
        for i in range(0, len(args), 2):
            mother = args[i]
            name = args[i+1]
            if mother == "Kailyn":
                kailyn_pos = i // 2 + 1
            if name == "Arnold":
                arnold_pos = i // 2 + 1
        return kailyn_pos is not None and arnold_pos is not None and arnold_pos > kailyn_pos
    
    var_list = []
    for house in houses:
        var_list.extend([f"mother_{house}", f"name_{house}"])
    problem.addConstraint(arnold_right_of_kailyn, var_list)
    
    # Clue 19: The one who only drinks water is directly left of the person who smokes Blue Master.
    for i in range(1, 6):
        problem.addConstraint(
            lambda drink, cigar: drink == "water" and cigar == "blue master",
            [f"drink_{i}", f"cigar_{i+1}"]
        )
    
    # Clue 20: The person who loves the spaghetti eater is somewhere to the left of the person who smokes many unique blends.
    def spaghetti_left_of_blends(*args):
        # args will be: food_1, cigar_1, food_2, cigar_2, ..., food_6, cigar_6
        spaghetti_pos = None
        blends_pos = None
        for i in range(0, len(args), 2):
            food = args[i]
            cigar = args[i+1]
            if food == "spaghetti":
                spaghetti_pos = i // 2 + 1
            if cigar == "blends":
                blends_pos = i // 2 + 1
        return spaghetti_pos is not None and blends_pos is not None and spaghetti_pos < blends_pos
    
    var_list = []
    for house in houses:
        var_list.extend([f"food_{house}", f"cigar_{house}"])
    problem.addConstraint(spaghetti_left_of_blends, var_list)
    
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
            lambda drink, food: (drink == "water") == (food == "stew"),
            [f"drink_{house}", f"food_{house}"]
        )
    
    # Clue 24: The Dunhill smoker is not in the second house.
    problem.addConstraint(lambda x: x != "dunhill", ["cigar_2"])
    
    # Clue 25: The person who likes milk is The person whose mother's name is Janelle.
    for house in houses:
        problem.addConstraint(
            lambda drink, mother: (drink == "milk") == (mother == "Janelle"),
            [f"drink_{house}", f"mother_{house}"]
        )
    
    # Clue 26: Eric is The person whose mother's name is Aniya.
    for house in houses:
        problem.addConstraint(
            lambda name, mother: (name == "Eric") == (mother == "Aniya"),
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