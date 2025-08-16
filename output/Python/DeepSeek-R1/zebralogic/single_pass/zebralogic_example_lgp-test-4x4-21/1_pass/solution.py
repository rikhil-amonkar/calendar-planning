import itertools
import json

def main():
    names = ['Eric', 'Peter', 'Alice', 'Arnold']
    cars = ['honda civic', 'tesla model 3', 'toyota camry', 'ford f150']
    birthdays = ['jan', 'april', 'sept', 'feb']
    hobbies = ['painting', 'cooking', 'gardening', 'photography']
    
    solution_found = False
    solution_rows = None
    
    for name_perm in itertools.permutations(names):
        peter_index = name_perm.index('Peter')
        arnold_index = name_perm.index('Arnold')
        alice_index = name_perm.index('Alice')
        
        for car_perm in itertools.permutations(cars):
            if car_perm[peter_index] != 'toyota camry':
                continue
            if car_perm[arnold_index] != 'tesla model 3':
                continue
            
            for birthday_perm in itertools.permutations(birthdays):
                if birthday_perm[1] == 'jan':
                    continue
                if birthday_perm[peter_index] != 'jan':
                    continue
                if birthday_perm[arnold_index] != 'april':
                    continue
                
                for hobby_perm in itertools.permutations(hobbies):
                    if hobby_perm[alice_index] != 'photography':
                        continue
                    
                    idx_feb = birthday_perm.index('feb')
                    if hobby_perm[idx_feb] != 'cooking':
                        continue
                    
                    if hobby_perm[alice_index] != 'photography':
                        continue
                    
                    idx_eric = name_perm.index('Eric')
                    if alice_index >= idx_eric:
                        continue
                    if alice_index >= peter_index:
                        continue
                    
                    found_adjacent = False
                    for i in range(3):
                        if car_perm[i] == 'honda civic' and car_perm[i+1] == 'tesla model 3':
                            found_adjacent = True
                            break
                    if not found_adjacent:
                        continue
                    
                    idx_tesla = arnold_index
                    idx_garden = hobby_perm.index('gardening')
                    if abs(idx_tesla - idx_garden) != 2:
                        continue
                    
                    solution_rows = []
                    for i in range(4):
                        house_num = str(i+1)
                        row = [house_num, name_perm[i], car_perm[i], birthday_perm[i], hobby_perm[i]]
                        solution_rows.append(row)
                    
                    solution_found = True
                    break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    
    if not solution_found:
        print('{"solution": {}}')
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result))

if __name__ == "__main__":
    main()