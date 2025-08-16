import itertools
import json

def main():
    names_list = ['Eric', 'Alice', 'Peter', 'Arnold']
    smoothies_list = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cars_list = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
    flowers_list = ['daffodils', 'roses', 'lilies', 'carnations']
    
    sports_fixed_start = ['tennis', 'soccer']
    sports_remaining_list = ['basketball', 'swimming']
    
    found_solution = None
    
    for names in itertools.permutations(names_list):
        for smoothies in itertools.permutations(smoothies_list):
            for sports23 in itertools.permutations(sports_remaining_list):
                sports = sports_fixed_start + list(sports23)
                for cars in itertools.permutations(cars_list):
                    for flowers in itertools.permutations(flowers_list):
                        if check_constraints(names, smoothies, sports, cars, flowers):
                            found_solution = (list(names), list(smoothies), list(sports), list(cars), list(flowers))
                            break
                    if found_solution:
                        break
                if found_solution:
                    break
            if found_solution:
                break
        if found_solution:
            break
            
    if found_solution:
        names, smoothies, sports, cars, flowers = found_solution
        rows = []
        for i in range(4):
            row = [str(i+1), names[i], smoothies[i], sports[i], cars[i], flowers[i]]
            rows.append(row)
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print('{"solution": {}}')

def check_constraints(names, smoothies, sports, cars, flowers):
    # Constraint 1 and 8: Eric has roses and Tesla Model 3
    for i in range(4):
        if names[i] == 'Eric':
            if flowers[i] != 'roses' or cars[i] != 'tesla model 3':
                return False
                
    # Constraint 2: Peter has dragonfruit smoothie
    for i in range(4):
        if names[i] == 'Peter':
            if smoothies[i] != 'dragonfruit':
                return False
                
    # Constraint 3: Desert smoothie lover owns Toyota Camry
    for i in range(4):
        if smoothies[i] == 'desert':
            if cars[i] != 'toyota camry':
                return False
                
    # Constraint 5: Toyota Camry and basketball are adjacent
    toyota_index = None
    basketball_index = None
    for i in range(4):
        if cars[i] == 'toyota camry':
            toyota_index = i
        if sports[i] == 'basketball':
            basketball_index = i
    if toyota_index is None or basketball_index is None:
        return False
    if abs(toyota_index - basketball_index) != 1:
        return False
        
    # Constraint 6: Arnold loves basketball
    for i in range(4):
        if names[i] == 'Arnold':
            if sports[i] != 'basketball':
                return False
                
    # Constraint 7: Honda Civic owner loves daffodils
    for i in range(4):
        if cars[i] == 'honda civic':
            if flowers[i] != 'daffodils':
                return False
                
    # Constraint 9: Watermelon smoothie not in first house
    for i in range(4):
        if smoothies[i] == 'watermelon':
            if i == 0:
                return False
                
    # Constraint 10: Honda Civic is to the right of desert smoothie lover
    desert_index = None
    for i in range(4):
        if smoothies[i] == 'desert':
            desert_index = i
            break
    if desert_index is None:
        return False
    found_honda = False
    for j in range(desert_index+1, 4):
        if cars[j] == 'honda civic':
            found_honda = True
            break
    if not found_honda:
        return False
        
    # Constraint 11: Basketball lover has lilies
    for i in range(4):
        if sports[i] == 'basketball':
            if flowers[i] != 'lilies':
                return False
                
    return True

if __name__ == '__main__':
    main()