import itertools
import json

def main():
    names = ['Eric', 'Peter', 'Arnold']
    smoothies = ['cherry', 'watermelon', 'desert']
    flowers = ['carnations', 'lilies', 'daffodils']
    animals = ['cat', 'horse', 'bird']
    hobbies = ['photography', 'cooking', 'gardening']
    
    perms_names = list(itertools.permutations(names))
    perms_smoothies = list(itertools.permutations(smoothies))
    perms_flowers = list(itertools.permutations(flowers))
    perms_animals = list(itertools.permutations(animals))
    perms_hobbies = list(itertools.permutations(hobbies))
    
    all_combinations = itertools.product(perms_names, perms_smoothies, perms_flowers, perms_animals, perms_hobbies)
    solution_assignment = None
    
    for n, s, f, a, h in all_combinations:
        assignment = []
        for i in range(3):
            assignment.append((n[i], s[i], f[i], a[i], h[i]))
        
        if check_constraints(assignment):
            solution_assignment = assignment
            break
    
    if solution_assignment is None:
        output = {"error": "No solution found"}
        print(json.dumps(output))
    else:
        header = ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"]
        rows = []
        for idx, house in enumerate(solution_assignment):
            house_num = str(idx + 1)
            row = [house_num] + list(house)
            rows.append(row)
        
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(result))

def check_constraints(assign):
    # Constraint 8: Photography enthusiast is Eric
    found8 = False
    for i in range(3):
        if assign[i][4] == 'photography' and assign[i][0] == 'Eric':
            found8 = True
            break
    if not found8:
        return False
    
    # Constraint 2: Bird keeper likes cherry smoothie
    for i in range(3):
        if assign[i][3] == 'bird':
            if assign[i][1] != 'cherry':
                return False
            break
    
    # Constraint 3: Cooking enthusiast likes desert smoothie
    for i in range(3):
        if assign[i][4] == 'cooking':
            if assign[i][1] != 'desert':
                return False
            break
    
    # Constraint 4: Gardening enthusiast likes carnations
    for i in range(3):
        if assign[i][4] == 'gardening':
            if assign[i][2] != 'carnations':
                return False
            break
    
    # Constraint 5: Cooking enthusiast is directly left of Peter
    cooking_index = None
    peter_index = None
    for i in range(3):
        if assign[i][4] == 'cooking':
            cooking_index = i
        if assign[i][0] == 'Peter':
            peter_index = i
    if cooking_index is None or peter_index is None:
        return False
    if cooking_index != peter_index - 1:
        return False
    
    # Constraint 6: Daffodils enthusiast likes desert smoothie
    for i in range(3):
        if assign[i][2] == 'daffodils':
            if assign[i][1] != 'desert':
                return False
            break
    
    # Constraint 7: Watermelon smoothie lover keeps horses
    for i in range(3):
        if assign[i][1] == 'watermelon':
            if assign[i][3] != 'horse':
                return False
            break
    
    # Constraint 1: Horse keeper and photography enthusiast are adjacent
    horse_index = None
    photo_index = None
    for i in range(3):
        if assign[i][3] == 'horse':
            horse_index = i
        if assign[i][4] == 'photography':
            photo_index = i
    if horse_index is None or photo_index is None:
        return False
    if abs(horse_index - photo_index) != 1:
        return False
    
    return True

if __name__ == '__main__':
    main()