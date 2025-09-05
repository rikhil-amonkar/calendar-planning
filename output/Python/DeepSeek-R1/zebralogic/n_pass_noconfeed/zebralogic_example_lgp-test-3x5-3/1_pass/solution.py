import itertools
import json

def main():
    # Define the attributes and their possible values
    names = ['Eric', 'Peter', 'Arnold']
    smoothies = ['cherry', 'watermelon', 'desert']
    flowers = ['carnations', 'lilies', 'daffodils']
    animals = ['cat', 'horse', 'bird']
    hobbies = ['photography', 'cooking', 'gardening']
    
    # Generate all permutations for each attribute
    names_perms = list(itertools.permutations(names))
    smoothies_perms = list(itertools.permutations(smoothies))
    flowers_perms = list(itertools.permutations(flowers))
    animals_perms = list(itertools.permutations(animals))
    hobbies_perms = list(itertools.permutations(hobbies))
    
    # Iterate over all combinations of permutations
    for n_perm in names_perms:
        for s_perm in smoothies_perms:
            for f_perm in flowers_perms:
                for a_perm in animals_perms:
                    for h_perm in hobbies_perms:
                        # Create assignment for the three houses
                        assignment = []
                        for i in range(3):
                            house = {
                                'House': i+1,
                                'Name': n_perm[i],
                                'Smoothie': s_perm[i],
                                'Flower': f_perm[i],
                                'Animal': a_perm[i],
                                'Hobby': h_perm[i]
                            }
                            assignment.append(house)
                        
                        # Check all constraints
                        if check_constraints(assignment):
                            # Format the solution as required
                            rows = []
                            for house in assignment:
                                rows.append([
                                    str(house['House']),
                                    house['Name'],
                                    house['Smoothie'],
                                    house['Flower'],
                                    house['Animal'],
                                    house['Hobby']
                                ])
                            
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                                    "rows": rows
                                }
                            }
                            
                            # Output the JSON
                            print(json.dumps(solution, indent=2))
                            return

def check_constraints(assignment):
    # Clue 1: Horse keeper and photography enthusiast are adjacent
    h_house = None
    p_house = None
    for house in assignment:
        if house['Animal'] == 'horse':
            h_house = house['House']
        if house['Hobby'] == 'photography':
            p_house = house['House']
    if abs(h_house - p_house) != 1:
        return False
    
    # Clue 2: Bird keeper likes cherry smoothie
    for house in assignment:
        if house['Animal'] == 'bird' and house['Smoothie'] != 'cherry':
            return False
    
    # Clue 3: Cooking hobbyist likes desert smoothie
    for house in assignment:
        if house['Hobby'] == 'cooking' and house['Smoothie'] != 'desert':
            return False
    
    # Clue 4: Gardening hobbyist likes carnations
    for house in assignment:
        if house['Hobby'] == 'gardening' and house['Flower'] != 'carnations':
            return False
    
    # Clue 5: Cooking hobbyist is directly left of Peter
    cooking_house = None
    peter_house = None
    for house in assignment:
        if house['Hobby'] == 'cooking':
            cooking_house = house['House']
        if house['Name'] == 'Peter':
            peter_house = house['House']
    if cooking_house + 1 != peter_house:
        return False
    
    # Clue 6: Daffodils lover likes desert smoothie
    for house in assignment:
        if house['Flower'] == 'daffodils' and house['Smoothie'] != 'desert':
            return False
    
    # Clue 7: Watermelon smoothie lover keeps horses
    for house in assignment:
        if house['Smoothie'] == 'watermelon' and house['Animal'] != 'horse':
            return False
    
    # Clue 8: Photography enthusiast is Eric
    for house in assignment:
        if house['Hobby'] == 'photography' and house['Name'] != 'Eric':
            return False
    
    return True

if __name__ == "__main__":
    main()