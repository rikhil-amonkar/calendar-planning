import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5]
    names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    foods = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]
    
    # Add variables for each attribute including house
    problem.addVariables(["house"], houses)
    problem.addVariables(["name"], names)
    problem.addVariables(["height"], heights)
    problem.addVariables(["food"], foods)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), ["house"])
    problem.addConstraint(AllDifferentConstraint(), ["name"])
    problem.addConstraint(AllDifferentConstraint(), ["height"])
    problem.addConstraint(AllDifferentConstraint(), ["food"])
    
    # Clue 1: Alice is the person who is short.
    problem.addConstraint(lambda name, height: not (name == "Alice") or (height == "short"), 
                         ["name", "height"])
    
    # Clue 2: The person who is tall is in the third house.
    # Clue 6: The person who is a pizza lover is the person who is tall.
    # Clue 7: Eric is the person who is tall.
    # These clues together mean: House 3 has Eric, tall height, and pizza food
    problem.addConstraint(lambda name, height, food, house: 
                         not (house == 3) or (name == "Eric" and height == "tall" and food == "pizza"),
                         ["name", "height", "food", "house"])
    
    # Clue 3: The person who has an average height is not in the second house.
    problem.addConstraint(lambda height, house: not (height == "average") or (house != 2),
                         ["height", "house"])
    
    # Clue 4: The person who has an average height is somewhere to the left of the person who loves the stew.
    # We need to compare houses for average height person vs stew person
    def clue4_constraint(avg_house, avg_height, stew_house, stew_food):
        if avg_height == "average" and stew_food == "stew":
            return avg_house < stew_house
        return True
    
    problem.addConstraint(clue4_constraint, ["house", "height", "house", "food"])
    
    # Clue 5: The person who loves stir fry is Arnold.
    problem.addConstraint(lambda name, food: not (food == "stir fry") or (name == "Arnold"),
                         ["name", "food"])
    
    # Clue 8: Bob is somewhere to the right of Arnold.
    # We need to compare Bob's house vs Arnold's house
    def clue8_constraint(bob_house, bob_name, arnold_house, arnold_name):
        if bob_name == "Bob" and arnold_name == "Arnold":
            return bob_house > arnold_house
        return True
    
    problem.addConstraint(clue8_constraint, ["house", "name", "house", "name"])
    
    # Clue 9: The person who loves eating grilled cheese is somewhere to the right of Eric.
    def clue9_constraint(gc_house, gc_food, eric_house, eric_name):
        if gc_food == "grilled cheese" and eric_name == "Eric":
            return gc_house > eric_house
        return True
    
    problem.addConstraint(clue9_constraint, ["house", "food", "house", "name"])
    
    # Clue 10: The person who is very short is somewhere to the left of Arnold.
    def clue10_constraint(vs_house, vs_height, arnold_house, arnold_name):
        if vs_height == "very short" and arnold_name == "Arnold":
            return vs_house < arnold_house
        return True
    
    problem.addConstraint(clue10_constraint, ["house", "height", "house", "name"])
    
    # Generate all possible solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Height", "Food"], "rows": []}}
    
    # Convert to house-based representation
    house_data = {}
    for sol in solutions:
        house = sol["house"]
        house_data[house] = {
            "name": sol["name"],
            "height": sol["height"], 
            "food": sol["food"]
        }
    
    # Create rows in house order
    rows = []
    for house in sorted(house_data.keys()):
        data = house_data[house]
        rows.append([str(house), data["name"], data["height"], data["food"]])
    
    return {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))