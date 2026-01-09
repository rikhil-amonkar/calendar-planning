import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"mother_{house}", mothers)
        problem.addVariable(f"pet_{house}", pets)
    
    # All names, mothers, and pets must be different
    problem.addConstraint(AllDifferentConstraint(), [f"name_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"mother_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"pet_{h}" for h in houses])
    
    # Helper function to get house number for an attribute
    def get_house_for_attribute(solution, attribute_type, value):
        for house in houses:
            if solution[f"{attribute_type}_{house}"] == value:
                return house
        return None
    
    # Clue 1: Bob is not in the second house
    problem.addConstraint(lambda name_2: name_2 != "Bob", ["name_2"])
    
    # Clue 2: Two houses between cat and rabbit
    def cat_rabbit_distance(*args):
        solution = {f"pet_{h}": args[i] for i, h in enumerate(houses)}
        cat_house = get_house_for_attribute(solution, "pet", "cat")
        rabbit_house = get_house_for_attribute(solution, "pet", "rabbit")
        if cat_house and rabbit_house:
            return abs(cat_house - rabbit_house) == 3
        return True
    problem.addConstraint(cat_rabbit_distance, [f"pet_{h}" for h in houses])
    
    # Clue 3: Cat directly left of Holly
    def cat_left_of_holly(*args):
        solution = {f"pet_{h}": args[i] for i, h in enumerate(houses)}
        mother_solution = {f"mother_{h}": args[i + len(houses)] for i, h in enumerate(houses)}
        
        cat_house = get_house_for_attribute(solution, "pet", "cat")
        holly_house = get_house_for_attribute(mother_solution, "mother", "Holly")
        
        if cat_house and holly_house:
            return holly_house == cat_house + 1
        return True
    problem.addConstraint(cat_left_of_holly, [f"pet_{h}" for h in houses] + [f"mother_{h}" for h in houses])
    
    # Clue 4: Hamster directly left of rabbit
    def hamster_left_of_rabbit(*args):
        solution = {f"pet_{h}": args[i] for i, h in enumerate(houses)}
        hamster_house = get_house_for_attribute(solution, "pet", "hamster")
        rabbit_house = get_house_for_attribute(solution, "pet", "rabbit")
        
        if hamster_house and rabbit_house:
            return rabbit_house == hamster_house + 1
        return True
    problem.addConstraint(hamster_left_of_rabbit, [f"pet_{h}" for h in houses])
    
    # Clue 5: Rabbit owner is Eric
    def rabbit_owner_is_eric(*args):
        pet_solution = {f"pet_{h}": args[i] for i, h in enumerate(houses)}
        name_solution = {f"name_{h}": args[i + len(houses)] for i, h in enumerate(houses)}
        
        rabbit_house = get_house_for_attribute(pet_solution, "pet", "rabbit")
        if rabbit_house:
            return name_solution[f"name_{rabbit_house}"] == "Eric"
        return True
    problem.addConstraint(rabbit_owner_is_eric, [f"pet_{h}" for h in houses] + [f"name_{h}" for h in houses])
    
    # Clue 6: One house between dog and cat
    def dog_cat_distance(*args):
        solution = {f"pet_{h}": args[i] for i, h in enumerate(houses)}
        dog_house = get_house_for_attribute(solution, "pet", "dog")
        cat_house = get_house_for_attribute(solution, "pet", "cat")
        
        if dog_house and cat_house:
            return abs(dog_house - cat_house) == 2
        return True
    problem.addConstraint(dog_cat_distance, [f"pet_{h}" for h in houses])
    
    # Clue 7: Cat owner's mother is Janelle
    def cat_owner_mother_janelle(*args):
        pet_solution = {f"pet_{h}": args[i] for i, h in enumerate(houses)}
        mother_solution = {f"mother_{h}": args[i + len(houses)] for i, h in enumerate(houses)}
        
        cat_house = get_house_for_attribute(pet_solution, "pet", "cat")
        if cat_house:
            return mother_solution[f"mother_{cat_house}"] == "Janelle"
        return True
    problem.addConstraint(cat_owner_mother_janelle, [f"pet_{h}" for h in houses] + [f"mother_{h}" for h in houses])
    
    # Clue 8: Alice directly left of Carol
    def alice_left_of_carol(*args):
        solution = {f"name_{h}": args[i] for i, h in enumerate(houses)}
        alice_house = get_house_for_attribute(solution, "name", "Alice")
        carol_house = get_house_for_attribute(solution, "name", "Carol")
        
        if alice_house and carol_house:
            return carol_house == alice_house + 1
        return True
    problem.addConstraint(alice_left_of_carol, [f"name_{h}" for h in houses])
    
    # Clue 9: Carol's mother is Aniya
    def carol_mother_aniya(*args):
        name_solution = {f"name_{h}": args[i] for i, h in enumerate(houses)}
        mother_solution = {f"mother_{h}": args[i + len(houses)] for i, h in enumerate(houses)}
        
        carol_house = get_house_for_attribute(name_solution, "name", "Carol")
        if carol_house:
            return mother_solution[f"mother_{carol_house}"] == "Aniya"
        return True
    problem.addConstraint(carol_mother_aniya, [f"name_{h}" for h in houses] + [f"mother_{h}" for h in houses])
    
    # Clue 10: Arnold has a cat
    def arnold_has_cat(*args):
        name_solution = {f"name_{h}": args[i] for i, h in enumerate(houses)}
        pet_solution = {f"pet_{h}": args[i + len(houses)] for i, h in enumerate(houses)}
        
        arnold_house = get_house_for_attribute(name_solution, "name", "Arnold")
        if arnold_house:
            return pet_solution[f"pet_{arnold_house}"] == "cat"
        return True
    problem.addConstraint(arnold_has_cat, [f"name_{h}" for h in houses] + [f"pet_{h}" for h in houses])
    
    # Clue 11: Kailyn's child owns rabbit
    def kailyn_child_has_rabbit(*args):
        mother_solution = {f"mother_{h}": args[i] for i, h in enumerate(houses)}
        pet_solution = {f"pet_{h}": args[i + len(houses)] for i, h in enumerate(houses)}
        
        kailyn_house = get_house_for_attribute(mother_solution, "mother", "Kailyn")
        if kailyn_house:
            return pet_solution[f"pet_{kailyn_house}"] == "rabbit"
        return True
    problem.addConstraint(kailyn_child_has_rabbit, [f"mother_{h}" for h in houses] + [f"pet_{h}" for h in houses])
    
    # Clue 12: Fish owner's mother is Sarah
    def fish_owner_mother_sarah(*args):
        pet_solution = {f"pet_{h}": args[i] for i, h in enumerate(houses)}
        mother_solution = {f"mother_{h}": args[i + len(houses)] for i, h in enumerate(houses)}
        
        fish_house = get_house_for_attribute(pet_solution, "pet", "fish")
        if fish_house:
            return mother_solution[f"mother_{fish_house}"] == "Sarah"
        return True
    problem.addConstraint(fish_owner_mother_sarah, [f"pet_{h}" for h in houses] + [f"mother_{h}" for h in houses])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Mother", "Pet"], "rows": []}}
    
    # Convert solution to the required format
    solution = solutions[0]
    rows = []
    
    for house in houses:
        name = solution[f"name_{house}"]
        mother = solution[f"mother_{house}"]
        pet = solution[f"pet_{house}"]
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