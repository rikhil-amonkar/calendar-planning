#!/usr/bin/env python3
import json

# Lists of possible attributes.
NAMES = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
MOTHERS = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
PETS = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

def is_valid(assignment):
    """
    Check whether a partial (or complete) assignment is valid with respect to the puzzle constraints.
    The assignment is a list of tuples, where each tuple is (name, mother, pet).
    Houses are numbered 0 to len(assignment)-1 corresponding to houses 1 to n.
    """
    n = len(assignment)
    # Check individual house constraints.
    for i in range(n):
        name, mother, pet = assignment[i]
        
        # Constraint 1: Bob is not in the second house (house index 1).
        if i == 1 and name == "Bob":
            return False
        
        # Constraint 10 and 7: Arnold is the person who has a cat AND the cat's mother must be Janelle.
        if name == "Arnold":
            if pet != "cat" or mother != "Janelle":
                return False
        if pet == "cat":
            if name != "Arnold" or mother != "Janelle":
                return False

        # Constraint 5 and 11: The person who owns a rabbit is Eric and his mother is Kailyn.
        if name == "Eric":
            if pet != "rabbit" or mother != "Kailyn":
                return False
        if pet == "rabbit":
            if name != "Eric" or mother != "Kailyn":
                return False
        if mother == "Kailyn":
            if pet != "rabbit":
                return False

        # Constraint 12: The person with the aquarium of fish has mother Sarah.
        if pet == "fish":
            if mother != "Sarah":
                return False
        if mother == "Sarah":
            if pet != "fish":
                return False

        # Constraint 9: Carol is the person whose mother's name is Aniya.
        if name == "Carol":
            if mother != "Aniya":
                return False
        if mother == "Aniya":
            if name != "Carol":
                return False

        # Additional positional check: The first house cannot be Carol.
        if i == 0 and name == "Carol":
            return False

        # If the assignment is complete (n==6), the last house must not have attributes that demand a right neighbor.
        if n == 6 and i == 5:
            # Constraint 8: Alice must be immediately left of Carol, so Alice cannot be in the last house.
            if name == "Alice":
                return False
            # Constraint 4: The hamster must be immediately left of the rabbit.
            if pet == "hamster":
                return False
            # Constraint 3: The person with the cat must be immediately left of a house with mother Holly.
            if pet == "cat":
                return False

    # Check adjacent constraints for houses that are assigned.
    for i in range(n - 1):
        name_i, mother_i, pet_i = assignment[i]
        name_next, mother_next, pet_next = assignment[i+1]
        
        # Constraint 3: The person with a cat is directly left of the person whose mother's name is Holly.
        if pet_i == "cat":
            if mother_next != "Holly":
                return False
        if mother_next == "Holly":
            if pet_i != "cat":
                return False

        # Constraint 4: The person with the hamster is directly left of the person who owns a rabbit.
        if pet_i == "hamster":
            if pet_next != "rabbit":
                return False
        if pet_next == "rabbit":
            if pet_i != "hamster":
                return False

        # Constraint 8: Alice is directly left of Carol.
        if name_i == "Alice":
            if name_next != "Carol":
                return False
        if name_next == "Carol":
            if name_i != "Alice":
                return False

    # Global relative constraints (non-adjacent).
    # Constraint 6: There is one house between the person who owns a dog and the person who has a cat.
    dog_index = None
    cat_index = None
    for i in range(n):
        if assignment[i][2] == "dog":
            dog_index = i
        if assignment[i][2] == "cat":
            cat_index = i
    if dog_index is not None and cat_index is not None:
        if abs(dog_index - cat_index) != 2:
            return False

    # Constraint 2: There are two houses between the person who has a cat and the person who owns a rabbit.
    rabbit_index = None
    for i in range(n):
        if assignment[i][2] == "rabbit":
            rabbit_index = i
    if cat_index is not None and rabbit_index is not None:
        if abs(cat_index - rabbit_index) != 3:
            return False

    return True

def backtrack(index, assignment, names_left, mothers_left, pets_left):
    """
    Recursively assign attributes to houses.
    index: current house index (0-based)
    assignment: list of already assigned houses (tuples of (name, mother, pet))
    names_left, mothers_left, pets_left: remaining options.
    """
    if index == 6:
        if is_valid(assignment):
            return assignment
        else:
            return None

    for name in names_left:
        for mother in mothers_left:
            for pet in pets_left:
                new_assignment = assignment + [(name, mother, pet)]
                if not is_valid(new_assignment):
                    continue
                new_names = names_left.copy()
                new_names.remove(name)
                new_mothers = mothers_left.copy()
                new_mothers.remove(mother)
                new_pets = pets_left.copy()
                new_pets.remove(pet)
                result = backtrack(index + 1, new_assignment, new_names, new_mothers, new_pets)
                if result is not None:
                    return result
    return None

def main():
    solution = backtrack(0, [], NAMES, MOTHERS, PETS)
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Mother", "Pet"], "rows": []}}
    else:
        # Format the solution: houses are numbered 1 to 6.
        rows = []
        for i, (name, mother, pet) in enumerate(solution):
            rows.append([str(i+1), name, mother, pet])
        output = {
            "solution": {
                "header": ["House", "Name", "Mother", "Pet"],
                "rows": rows
            }
        }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()