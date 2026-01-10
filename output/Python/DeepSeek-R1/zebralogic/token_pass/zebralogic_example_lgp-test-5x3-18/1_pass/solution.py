import json

def main():
    # Define the domains
    names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
    flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
    animals = ['dog', 'horse', 'cat', 'bird', 'fish']
    
    # Initialize assignment and available sets
    assignment = [None] * 5
    available_names = set(names)
    available_flowers = set(flowers)
    available_animals = set(animals)
    
    # Constraint functions
    def check_constraints(assign):
        # Convert assignment to list of tuples (name, flower, animal) for each house
        # Constraint 1: Alice is in the second house.
        if assign[1] is not None and assign[1][0] != 'Alice':
            return False
        
        # Constraint 2: The person who loves lilies is the bird keeper.
        for house in assign:
            if house is not None:
                name, flower, animal = house
                if flower == 'lilies' and animal != 'bird':
                    return False
                if animal == 'bird' and flower != 'lilies':
                    return False
        
        # Constraint 3: Peter is right of the tulips lover.
        peter_house = None
        tulips_house = None
        for i, house in enumerate(assign):
            if house is not None:
                if house[0] == 'Peter':
                    peter_house = i
                if house[1] == 'tulips':
                    tulips_house = i
        if peter_house is not None and tulips_house is not None:
            if peter_house <= tulips_house:
                return False
        
        # Constraint 4: Fish enthusiast loves daffodils.
        for house in assign:
            if house is not None:
                name, flower, animal = house
                if animal == 'fish' and flower != 'daffodils':
                    return False
                if flower == 'daffodils' and animal != 'fish':
                    return False
        
        # Constraint 5: Horse keeper is Eric.
        for house in assign:
            if house is not None:
                name, flower, animal = house
                if animal == 'horse' and name != 'Eric':
                    return False
                if name == 'Eric' and animal != 'horse':
                    return False
        
        # Constraint 6: Two houses between dog owner and Bob.
        dog_house = None
        bob_house = None
        for i, house in enumerate(assign):
            if house is not None:
                if house[2] == 'dog':
                    dog_house = i
                if house[0] == 'Bob':
                    bob_house = i
        if dog_house is not None and bob_house is not None:
            if abs(dog_house - bob_house) != 3:
                return False
        
        # Constraint 7: Fish enthusiast directly left of Bob.
        fish_house = None
        bob_house = None
        for i, house in enumerate(assign):
            if house is not None:
                if house[2] == 'fish':
                    fish_house = i
                if house[0] == 'Bob':
                    bob_house = i
        if fish_house is not None and bob_house is not None:
            if fish_house + 1 != bob_house:
                return False
        
        # Constraint 8: Alice directly left of horse keeper.
        if assign[1] is not None and assign[1][0] != 'Alice':
            return False
        if assign[2] is not None and assign[2][2] != 'horse':
            return False
        
        # Constraint 9: Carnations directly left of tulips.
        carnations_house = None
        tulips_house = None
        for i, house in enumerate(assign):
            if house is not None:
                if house[1] == 'carnations':
                    carnations_house = i
                if house[1] == 'tulips':
                    tulips_house = i
        if carnations_house is not None and tulips_house is not None:
            if carnations_house + 1 != tulips_house:
                return False
        
        # Constraint 10: Cat lover not in first house.
        if assign[0] is not None and assign[0][2] == 'cat':
            return False
        
        return True

    # Backtracking search
    def backtrack(assign, avail_names, avail_flowers, avail_animals, current_house):
        if current_house == 5:
            return assign
        
        for name in list(avail_names):
            for flower in list(avail_flowers):
                for animal in list(avail_animals):
                    assign[current_house] = (name, flower, animal)
                    new_avail_names = avail_names - {name}
                    new_avail_flowers = avail_flowers - {flower}
                    new_avail_animals = avail_animals - {animal}
                    
                    if check_constraints(assign):
                        result = backtrack(assign, new_avail_names, new_avail_flowers, new_avail_animals, current_house+1)
                        if result is not None:
                            return result
                    
                    assign[current_house] = None
        
        return None

    # Solve the puzzle
    solution = backtrack(assignment, available_names, available_flowers, available_animals, 0)
    
    # Format the solution as JSON
    if solution is None:
        print('{"solution": {}}')
    else:
        rows = []
        for i, house in enumerate(solution):
            rows.append([str(i+1), house[0], house[1], house[2]])
        
        output = {
            "solution": {
                "header": ["House", "Name", "Flower", "Animal"],
                "rows": rows
            }
        }
        print(json.dumps(output))

if __name__ == '__main__':
    main()