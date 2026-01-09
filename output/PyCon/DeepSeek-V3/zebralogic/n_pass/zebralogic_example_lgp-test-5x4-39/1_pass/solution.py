import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5]
    names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights = ["very tall", "tall", "very short", "average", "short"]
    foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]
    
    # Add variables for each attribute
    problem.addVariables(["name"], names)
    problem.addVariables(["hobby"], hobbies)
    problem.addVariables(["height"], heights)
    problem.addVariables(["food"], foods)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), ["name"])
    problem.addConstraint(AllDifferentConstraint(), ["hobby"])
    problem.addConstraint(AllDifferentConstraint(), ["height"])
    problem.addConstraint(AllDifferentConstraint(), ["food"])
    
    # Clue 1: Bob is the photography enthusiast.
    problem.addConstraint(lambda name, hobby: not (name == "Bob") or (hobby == "photography"), ["name", "hobby"])
    
    # Clue 2: The person who loves eating grilled cheese is the person who is tall.
    problem.addConstraint(lambda food, height: not (food == "grilled cheese") or (height == "tall"), ["food", "height"])
    
    # Clue 3: Peter is not in the second house.
    problem.addConstraint(lambda name: not (name == "Peter"), ["name"], [2])
    
    # Clue 4: The person who is tall is directly left of the person who loves stir fry.
    problem.addConstraint(lambda height_left, height_right, food_left, food_right: 
                         not (height_left == "tall") or (food_right == "stir fry"), 
                         ["height", "height", "food", "food"], [(1,2), (2,3), (3,4), (4,5)])
    
    # Clue 5: The person who loves cooking is the person who has an average height.
    problem.addConstraint(lambda hobby, height: not (hobby == "cooking") or (height == "average"), ["hobby", "height"])
    
    # Clue 6: Alice is directly left of the person who is a pizza lover.
    problem.addConstraint(lambda name_left, name_right, food_left, food_right: 
                         not (name_left == "Alice") or (food_right == "pizza"), 
                         ["name", "name", "food", "food"], [(1,2), (2,3), (3,4), (4,5)])
    
    # Clue 7: The person who loves the spaghetti eater is not in the second house.
    problem.addConstraint(lambda food: not (food == "spaghetti"), ["food"], [2])
    
    # Clue 8: Eric is not in the fifth house.
    problem.addConstraint(lambda name: not (name == "Eric"), ["name"], [5])
    
    # Clue 9: The person who is short is Peter.
    problem.addConstraint(lambda name, height: not (height == "short") or (name == "Peter"), ["name", "height"])
    
    # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
    problem.addConstraint(lambda height_left, height_right, hobby_left, hobby_right: 
                         (height_left == "average" and hobby_right == "gardening") or 
                         (height_right == "average" and hobby_left == "gardening") or 
                         (height_left != "average" and height_right != "average"), 
                         ["height", "height", "hobby", "hobby"], [(1,2), (2,3), (3,4), (4,5)])
    
    # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    problem.addConstraint(lambda hobby_left, hobby_right, food_left, food_right: 
                         not (hobby_left == "painting") or (food_right == "grilled cheese"), 
                         ["hobby", "hobby", "food", "food"], [(1,2), (2,3), (3,4), (4,5)])
    
    # Clue 12: The person who is very short is in the fifth house.
    problem.addConstraint(lambda height: height == "very short", ["height"], [5])
    
    # Clue 13: The person who is tall is in the third house.
    problem.addConstraint(lambda height: height == "tall", ["height"], [3])
    
    # Clue 14: Alice is somewhere to the right of the photography enthusiast.
    def alice_right_of_photographer(solution):
        photo_house = None
        alice_house = None
        for house in houses:
            if solution[f"name_{house}"] == "Alice":
                alice_house = house
            if solution[f"hobby_{house}"] == "photography":
                photo_house = house
        return alice_house > photo_house if (photo_house and alice_house) else True
    
    # Add all variables for constraint solving
    for house in houses:
        problem.addVariables([f"name_{house}", f"hobby_{house}", f"height_{house}", f"food_{house}"], 
                           [names, hobbies, heights, foods])
    
    # Add constraint for clue 14
    problem.addConstraint(alice_right_of_photographer, 
                         [f"name_{house}" for house in houses] + [f"hobby_{house}" for house in houses])
    
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