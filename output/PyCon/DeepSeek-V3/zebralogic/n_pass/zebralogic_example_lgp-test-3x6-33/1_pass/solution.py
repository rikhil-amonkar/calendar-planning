import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1, 2, 3)
    houses = [1, 2, 3]
    
    # Define possible values for each attribute
    names = ["Arnold", "Eric", "Peter"]
    flowers = ["carnations", "lilies", "daffodils"]
    hair_colors = ["black", "brown", "blonde"]
    sports = ["soccer", "basketball", "tennis"]
    house_styles = ["colonial", "ranch", "victorian"]
    pets = ["fish", "dog", "cat"]
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"flower_{house}", flowers)
        problem.addVariable(f"hair_{house}", hair_colors)
        problem.addVariable(f"sport_{house}", sports)
        problem.addVariable(f"style_{house}", house_styles)
        problem.addVariable(f"pet_{house}", pets)
    
    # All attributes must be different across houses
    for attr in ["name", "flower", "hair", "sport", "style", "pet"]:
        problem.addConstraint(AllDifferentConstraint(), [f"{attr}_{house}" for house in houses])
    
    # Clue 1: The person who has a cat is the person who loves soccer.
    for house in houses:
        problem.addConstraint(
            lambda cat_pet, soccer_sport: cat_pet == "cat" and soccer_sport == "soccer" or cat_pet != "cat" and soccer_sport != "soccer",
            [f"pet_{house}", f"sport_{house}"]
        )
    
    # Clue 2: The person who has blonde hair is in the second house.
    problem.addConstraint(lambda hair: hair == "blonde", ["hair_2"])
    
    # Clue 3: The person who loves a bouquet of daffodils is the person who has blonde hair.
    for house in houses:
        problem.addConstraint(
            lambda flower, hair: (flower == "daffodils" and hair == "blonde") or (flower != "daffodils" and hair != "blonde"),
            [f"flower_{house}", f"hair_{house}"]
        )
    
    # Clue 4: Peter is the person who loves basketball.
    for house in houses:
        problem.addConstraint(
            lambda name, sport: (name == "Peter" and sport == "basketball") or (name != "Peter" and sport != "basketball"),
            [f"name_{house}", f"sport_{house}"]
        )
    
    # Clue 5: Arnold is directly left of the person in a ranch-style home.
    problem.addConstraint(lambda name1, style2: name1 == "Arnold" and style2 == "ranch", ["name_1", "style_2"])
    problem.addConstraint(lambda name2, style3: name2 == "Arnold" and style3 == "ranch", ["name_2", "style_3"])
    
    # Clue 6: The person who owns a dog is the person who loves basketball.
    for house in houses:
        problem.addConstraint(
            lambda pet, sport: (pet == "dog" and sport == "basketball") or (pet != "dog" and sport != "basketball"),
            [f"pet_{house}", f"sport_{house}"]
        )
    
    # Clue 7: The person who loves a carnations arrangement is directly left of the person who has blonde hair.
    problem.addConstraint(lambda flower1, hair2: flower1 == "carnations" and hair2 == "blonde", ["flower_1", "hair_2"])
    
    # Clue 8: The person who loves soccer is in the third house.
    problem.addConstraint(lambda sport: sport == "soccer", ["sport_3"])
    
    # Clue 9: Arnold is somewhere to the left of the person who has black hair.
    # This means Arnold's house number < black hair house number
    def arnold_left_of_black(arnold_house, black_hair_house):
        return arnold_house < black_hair_house
    
    # Find which house has Arnold and which has black hair
    arnold_houses = []
    black_hair_houses = []
    for house in houses:
        arnold_houses.append(f"name_{house}")
        black_hair_houses.append(f"hair_{house}")
    
    problem.addConstraint(
        arnold_left_of_black,
        [f"name_{house}" for house in houses] + [f"hair_{house}" for house in houses]
    )
    
    # Clue 10: The person living in a colonial-style house is in the third house.
    problem.addConstraint(lambda style: style == "colonial", ["style_3"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"flower_{house}"],
            solution[f"hair_{house}"],
            solution[f"sport_{house}"],
            solution[f"style_{house}"],
            solution[f"pet_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))