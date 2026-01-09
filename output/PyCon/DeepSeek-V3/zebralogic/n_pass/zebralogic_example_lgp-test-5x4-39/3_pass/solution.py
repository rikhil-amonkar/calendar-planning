import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5]
    names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights = ["very tall", "tall", "very short", "average", "short"]
    foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]
    
    # Add variables for each house with all attributes
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"hobby_{house}", hobbies)
        problem.addVariable(f"height_{house}", heights)
        problem.addVariable(f"food_{house}", foods)
    
    # All attributes must be different across houses
    problem.addConstraint(AllDifferentConstraint(), [f"name_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"hobby_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"height_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"food_{house}" for house in houses])
    
    # Clue 1: Bob is the photography enthusiast.
    for house in houses:
        problem.addConstraint(
            lambda name, hobby: (name != "Bob") or (hobby == "photography"),
            [f"name_{house}", f"hobby_{house}"]
        )
    
    # Clue 2: The person who loves eating grilled cheese is the person who is tall.
    for house in houses:
        problem.addConstraint(
            lambda food, height: (food != "grilled cheese") or (height == "tall"),
            [f"food_{house}", f"height_{house}"]
        )
    
    # Clue 3: Peter is not in the second house.
    problem.addConstraint(lambda name_2: name_2 != "Peter", ["name_2"])
    
    # Clue 4: The person who is tall is directly left of the person who loves stir fry.
    for i in range(1, 5):
        problem.addConstraint(
            lambda height_i, height_i1, food_i, food_i1: 
            (height_i != "tall") or (food_i1 == "stir fry"),
            [f"height_{i}", f"height_{i+1}", f"food_{i}", f"food_{i+1}"]
        )
    
    # Clue 5: The person who loves cooking is the person who has an average height.
    for house in houses:
        problem.addConstraint(
            lambda hobby, height: (hobby != "cooking") or (height == "average"),
            [f"hobby_{house}", f"height_{house}"]
        )
    
    # Clue 6: Alice is directly left of the person who is a pizza lover.
    for i in range(1, 5):
        problem.addConstraint(
            lambda name_i, name_i1, food_i, food_i1: 
            (name_i != "Alice") or (food_i1 == "pizza"),
            [f"name_{i}", f"name_{i+1}", f"food_{i}", f"food_{i+1}"]
        )
    
    # Clue 7: The person who loves the spaghetti eater is not in the second house.
    problem.addConstraint(lambda food_2: food_2 != "spaghetti", ["food_2"])
    
    # Clue 8: Eric is not in the fifth house.
    problem.addConstraint(lambda name_5: name_5 != "Eric", ["name_5"])
    
    # Clue 9: The person who is short is Peter.
    for house in houses:
        problem.addConstraint(
            lambda name, height: (height != "short") or (name == "Peter"),
            [f"name_{house}", f"height_{house}"]
        )
    
    # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
    for i in range(1, 5):
        problem.addConstraint(
            lambda height_i, height_i1, hobby_i, hobby_i1: 
            (height_i == "average" and hobby_i1 == "gardening") or 
            (height_i1 == "average" and hobby_i == "gardening"),
            [f"height_{i}", f"height_{i+1}", f"hobby_{i}", f"hobby_{i+1}"]
        )
    
    # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    for i in range(1, 5):
        problem.addConstraint(
            lambda hobby_i, hobby_i1, food_i, food_i1: 
            (hobby_i != "painting") or (food_i1 == "grilled cheese"),
            [f"hobby_{i}", f"hobby_{i+1}", f"food_{i}", f"food_{i+1}"]
        )
    
    # Clue 12: The person who is very short is in the fifth house.
    problem.addConstraint(lambda height_5: height_5 == "very short", ["height_5"])
    
    # Clue 13: The person who is tall is in the third house.
    problem.addConstraint(lambda height_3: height_3 == "tall", ["height_3"])
    
    # Clue 14: Alice is somewhere to the right of the photography enthusiast.
    def alice_right_of_photographer(*args):
        # args contains all name and hobby variables
        name_vars = args[:5]  # First 5 are names
        hobby_vars = args[5:]  # Next 5 are hobbies
        
        alice_house = None
        photo_house = None
        
        for i, (name, hobby) in enumerate(zip(name_vars, hobby_vars)):
            if name == "Alice":
                alice_house = i + 1
            if hobby == "photography":
                photo_house = i + 1
        
        return alice_house is not None and photo_house is not None and alice_house > photo_house
    
    all_vars = [f"name_{house}" for house in houses] + [f"hobby_{house}" for house in houses]
    problem.addConstraint(alice_right_of_photographer, all_vars)
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Hobby", "Height", "Food"], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        hobby = solution[f"hobby_{house}"]
        height = solution[f"height_{house}"]
        food = solution[f"food_{house}"]
        rows.append([str(house), name, hobby, height, food])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))