import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]
    
    # Add variables for each attribute
    problem.addVariables(["name"], names)
    problem.addVariables(["mother"], mothers)
    problem.addVariables(["pet"], pets)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), ["name"])
    problem.addConstraint(AllDifferentConstraint(), ["mother"])
    problem.addConstraint(AllDifferentConstraint(), ["pet"])
    
    # Clue 1: Bob is not in the second house
    problem.addConstraint(lambda name, house: not (name == "Bob" and house == 2), ["name", "house"])
    
    # Clue 2: Two houses between cat and rabbit
    problem.addConstraint(lambda cat_house, rabbit_house: abs(cat_house - rabbit_house) == 3, ["cat_house", "rabbit_house"])
    
    # Clue 3: Cat directly left of Holly
    problem.addConstraint(lambda cat_house, holly_house: holly_house == cat_house + 1, ["cat_house", "holly_house"])
    
    # Clue 4: Hamster directly left of rabbit
    problem.addConstraint(lambda hamster_house, rabbit_house: rabbit_house == hamster_house + 1, ["hamster_house", "rabbit_house"])
    
    # Clue 5: Rabbit owner is Eric
    problem.addConstraint(lambda name, pet: not (pet == "rabbit" and name != "Eric"), ["name", "pet"])
    
    # Clue 6: One house between dog and cat
    problem.addConstraint(lambda dog_house, cat_house: abs(dog_house - cat_house) == 2, ["dog_house", "cat_house"])
    
    # Clue 7: Cat owner's mother is Janelle
    problem.addConstraint(lambda mother, pet: not (pet == "cat" and mother != "Janelle"), ["mother", "pet"])
    
    # Clue 8: Alice directly left of Carol
    problem.addConstraint(lambda alice_house, carol_house: carol_house == alice_house + 1, ["alice_house", "carol_house"])
    
    # Clue 9: Carol's mother is Aniya
    problem.addConstraint(lambda name, mother: not (name == "Carol" and mother != "Aniya"), ["name", "mother"])
    
    # Clue 10: Arnold has a cat
    problem.addConstraint(lambda name, pet: not (name == "Arnold" and pet != "cat"), ["name", "pet"])
    
    # Clue 11: Kailyn's child owns rabbit
    problem.addConstraint(lambda mother, pet: not (mother == "Kailyn" and pet != "rabbit"), ["mother", "pet"])
    
    # Clue 12: Fish owner's mother is Sarah
    problem.addConstraint(lambda mother, pet: not (pet == "fish" and mother != "Sarah"), ["mother", "pet"])
    
    # Link positions to attributes
    for house in houses:
        problem.addVariables([f"name_{house}"], names)
        problem.addVariables([f"mother_{house}"], mothers)
        problem.addVariables([f"pet_{house}"], pets)
        
        # Each house has exactly one name, mother, and pet
        problem.addConstraint(lambda n, h=house: n == h, [f"name_{house}", "name"])
        problem.addConstraint(lambda m, h=house: m == h, [f"mother_{house}", "mother"])
        problem.addConstraint(lambda p, h=house: p == h, [f"pet_{house}", "pet"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Mother", "Pet"], "rows": []}}
    
    # Convert solution to the required format
    solution = solutions[0]
    rows = []
    
    for house in sorted(houses):
        name = next((n for n in names if solution.get(f"name_{n}") == house), None)
        mother = next((m for m in mothers if solution.get(f"mother_{m}") == house), None)
        pet = next((p for p in pets if solution.get(f"pet_{p}") == house), None)
        
        rows.append([str(house), name, mother, pet])
    
    return {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))