import json
from itertools import permutations

def solve():
    # Define all possible values
    names = ["Eric", "Peter", "Arnold"]
    drinks = ["milk", "water", "tea"]
    vacations = ["mountain", "city", "beach"]
    house_styles = ["colonial", "victorian", "ranch"]
    animals = ["cat", "bird", "horse"]
    birthdays = ["jan", "sept", "april"]
    
    houses = [1, 2, 3]
    
    # Generate all permutations for each attribute across 3 houses
    all_name_perms = list(permutations(names, 3))
    all_drink_perms = list(permutations(drinks, 3))
    all_vacation_perms = list(permutations(vacations, 3))
    all_style_perms = list(permutations(house_styles, 3))
    all_animal_perms = list(permutations(animals, 3))
    all_birthday_perms = list(permutations(birthdays, 3))
    
    solutions = []
    
    # Brute force search through all combinations
    for name_perm in all_name_perms:
        for drink_perm in all_drink_perms:
            for vacation_perm in all_vacation_perms:
                for style_perm in all_style_perms:
                    for animal_perm in all_animal_perms:
                        for birthday_perm in all_birthday_perms:
                            # Create assignment for each house
                            assignment = []
                            for i in range(3):
                                assignment.append({
                                    'house': i+1,
                                    'name': name_perm[i],
                                    'drink': drink_perm[i],
                                    'vacation': vacation_perm[i],
                                    'style': style_perm[i],
                                    'animal': animal_perm[i],
                                    'birthday': birthday_perm[i]
                                })
                            
                            # Check all constraints
                            valid = True
                            
                            # 1. Colonial house is somewhere to the left of milk drinker
                            colonial_index = None
                            milk_index = None
                            for i, a in enumerate(assignment):
                                if a['style'] == 'colonial':
                                    colonial_index = i
                                if a['drink'] == 'milk':
                                    milk_index = i
                            if colonial_index is None or milk_index is None or colonial_index >= milk_index:
                                valid = False
                            
                            # 2. City vacation is directly left of Victorian house
                            if valid:
                                city_index = None
                                victorian_index = None
                                for i, a in enumerate(assignment):
                                    if a['vacation'] == 'city':
                                        city_index = i
                                    if a['style'] == 'victorian':
                                        victorian_index = i
                                if city_index is None or victorian_index is None or city_index + 1 != victorian_index:
                                    valid = False
                            
                            # 3. January birthday is directly left of cat lover
                            if valid:
                                jan_index = None
                                cat_index = None
                                for i, a in enumerate(assignment):
                                    if a['birthday'] == 'jan':
                                        jan_index = i
                                    if a['animal'] == 'cat':
                                        cat_index = i
                                if jan_index is None or cat_index is None or jan_index + 1 != cat_index:
                                    valid = False
                            
                            # 4. Water drinker enjoys mountain retreats
                            if valid:
                                for a in assignment:
                                    if a['drink'] == 'water' and a['vacation'] != 'mountain':
                                        valid = False
                                        break
                                    if a['vacation'] == 'mountain' and a['drink'] != 'water':
                                        valid = False
                                        break
                            
                            # 5. Horse keeper is Peter
                            if valid:
                                horse_found = False
                                for a in assignment:
                                    if a['animal'] == 'horse' and a['name'] != 'Peter':
                                        valid = False
                                        break
                                    if a['name'] == 'Peter' and a['animal'] != 'horse':
                                        valid = False
                                        break
                            
                            # 6. Victorian house is somewhere to the right of beach vacation lover
                            if valid:
                                beach_index = None
                                victorian_index = None
                                for i, a in enumerate(assignment):
                                    if a['vacation'] == 'beach':
                                        beach_index = i
                                    if a['style'] == 'victorian':
                                        victorian_index = i
                                if beach_index is None or victorian_index is None or beach_index >= victorian_index:
                                    valid = False
                            
                            # 7. Peter prefers city breaks
                            if valid:
                                peter_city = False
                                for a in assignment:
                                    if a['name'] == 'Peter' and a['vacation'] == 'city':
                                        peter_city = True
                                        break
                                if not peter_city:
                                    valid = False
                            
                            # 8. Mountain retreat lover has April birthday
                            if valid:
                                for a in assignment:
                                    if a['vacation'] == 'mountain' and a['birthday'] != 'april':
                                        valid = False
                                        break
                                    if a['birthday'] == 'april' and a['vacation'] != 'mountain':
                                        valid = False
                                        break
                            
                            # 9. Eric drinks water
                            if valid:
                                eric_water = False
                                for a in assignment:
                                    if a['name'] == 'Eric' and a['drink'] == 'water':
                                        eric_water = True
                                        break
                                if not eric_water:
                                    valid = False
                            
                            # All attributes must be unique per category (already guaranteed by permutations)
                            
                            if valid:
                                solutions.append(assignment)
    
    # Convert solution to required format
    if solutions:
        # Take first solution (should be only one)
        solution = solutions[0]
        
        # Sort by house number
        solution.sort(key=lambda x: x['house'])
        
        rows = []
        for house in solution:
            rows.append([
                str(house['house']),
                house['name'],
                house['drink'],
                house['vacation'],
                house['style'],
                house['animal'],
                house['birthday']
            ])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                "rows": rows
            }
        }
        
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

if __name__ == "__main__":
    print(solve())