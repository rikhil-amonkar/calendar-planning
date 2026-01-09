from constraint import Problem
import json

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5]
    names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animals = ["dog", "horse", "cat", "bird", "fish"]
    
    # Add variables for each attribute
    problem.addVariables(["name"], names)
    problem.addVariables(["flower"], flowers)
    problem.addVariables(["animal"], animals)
    
    # Apply constraint that all attributes are different
    problem.addConstraint(lambda n1, n2, n3, n4, n5: len({n1, n2, n3, n4, n5}) == 5, 
                         ["name_1", "name_2", "name_3", "name_4", "name_5"])
    problem.addConstraint(lambda f1, f2, f3, f4, f5: len({f1, f2, f3, f4, f5}) == 5, 
                         ["flower_1", "flower_2", "flower_3", "flower_4", "flower_5"])
    problem.addConstraint(lambda a1, a2, a3, a4, a5: len({a1, a2, a3, a4, a5}) == 5, 
                         ["animal_1", "animal_2", "animal_3", "animal_4", "animal_5"])
    
    # Clue 1: Alice is in the second house
    problem.addConstraint(lambda name: name == "Alice", ["name_2"])
    
    # Clue 2: The person who loves lilies is the bird keeper
    for i in houses:
        problem.addConstraint(
            lambda flower, animal, house=i: not (flower == "lilies" and animal != "bird") and 
                                           not (animal == "bird" and flower != "lilies"),
            [f"flower_{i}", f"animal_{i}"]
        )
    
    # Clue 3: Peter is somewhere to the right of the person who loves tulips
    def peter_right_of_tulips(*names_flowers):
        names = names_flowers[:5]
        flowers = names_flowers[5:]
        
        tulips_house = None
        peter_house = None
        
        for i, (name, flower) in enumerate(zip(names, flowers)):
            if flower == "tulips":
                tulips_house = i
            if name == "Peter":
                peter_house = i
        
        if tulips_house is not None and peter_house is not None:
            return peter_house > tulips_house
        return True
    
    problem.addConstraint(peter_right_of_tulips, 
                         ["name_1", "name_2", "name_3", "name_4", "name_5",
                          "flower_1", "flower_2", "flower_3", "flower_4", "flower_5"])
    
    # Clue 4: The fish enthusiast is the person who loves daffodils
    for i in houses:
        problem.addConstraint(
            lambda flower, animal, house=i: not (flower == "daffodils" and animal != "fish") and 
                                           not (animal == "fish" and flower != "daffodils"),
            [f"flower_{i}", f"animal_{i}"]
        )
    
    # Clue 5: The person who keeps horses is Eric
    for i in houses:
        problem.addConstraint(
            lambda name, animal, house=i: not (animal == "horse" and name != "Eric") and 
                                         not (name == "Eric" and animal != "horse"),
            [f"name_{i}", f"animal_{i}"]
        )
    
    # Clue 6: There are two houses between the dog owner and Bob
    def two_houses_between_dog_bob(*animals_names):
        animals = animals_names[:5]
        names = animals_names[5:]
        
        dog_house = None
        bob_house = None
        
        for i, (animal, name) in enumerate(zip(animals, names)):
            if animal == "dog":
                dog_house = i
            if name == "Bob":
                bob_house = i
        
        if dog_house is not None and bob_house is not None:
            return abs(dog_house - bob_house) == 3
        return True
    
    problem.addConstraint(two_houses_between_dog_bob,
                         ["animal_1", "animal_2", "animal_3", "animal_4", "animal_5",
                          "name_1", "name_2", "name_3", "name_4", "name_5"])
    
    # Clue 7: The fish enthusiast is directly left of Bob
    def fish_left_of_bob(*animals_names):
        animals = animals_names[:5]
        names = animals_names[5:]
        
        for i in range(4):  # houses 1-4 (since fish must be left of Bob)
            if animals[i] == "fish" and names[i+1] == "Bob":
                return True
        return False
    
    problem.addConstraint(fish_left_of_bob,
                         ["animal_1", "animal_2", "animal_3", "animal_4", "animal_5",
                          "name_1", "name_2", "name_3", "name_4", "name_5"])
    
    # Clue 8: Alice is directly left of the person who keeps horses
    def alice_left_of_horses(*names_animals):
        names = names_animals[:5]
        animals = names_animals[5:]
        
        for i in range(4):  # houses 1-4
            if names[i] == "Alice" and animals[i+1] == "horse":
                return True
        return False
    
    problem.addConstraint(alice_left_of_horses,
                         ["name_1", "name_2", "name_3", "name_4", "name_5",
                          "animal_1", "animal_2", "animal_3", "animal_4", "animal_5"])
    
    # Clue 9: Carnations are directly left of tulips
    def carnations_left_of_tulips(*flowers):
        for i in range(4):  # houses 1-4
            if flowers[i] == "carnations" and flowers[i+1] == "tulips":
                return True
        return False
    
    problem.addConstraint(carnations_left_of_tulips,
                         ["flower_1", "flower_2", "flower_3", "flower_4", "flower_5"])
    
    # Clue 10: The cat lover is not in the first house
    problem.addConstraint(lambda animal: animal != "cat", ["animal_1"])
    
    # Get solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Flower", "Animal"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        flower = solution[f"flower_{house}"]
        animal = solution[f"animal_{house}"]
        rows.append([str(house), name, flower, animal])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Flower", "Animal"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))