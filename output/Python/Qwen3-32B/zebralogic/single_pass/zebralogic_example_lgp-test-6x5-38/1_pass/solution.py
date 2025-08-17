import itertools
import json

names = ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter']
birthdays = ['feb', 'mar', 'sept', 'jan', 'may', 'april']
foods = ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
heights = ['very short', 'average', 'super tall', 'short', 'very tall', 'tall']
cars = ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic']

for name_perm in itertools.permutations(names):
    eric_pos = name_perm.index('Eric')
    bob_pos = name_perm.index('Bob')
    carol_pos = name_perm.index('Carol')
    alice_pos = name_perm.index('Alice')
    peter_pos = name_perm.index('Peter')
    
    for birthday_perm in itertools.permutations(birthdays):
        if birthday_perm[eric_pos] != 'jan':
            continue
        
        may_pos = birthday_perm.index('may')
        if may_pos >= carol_pos:
            continue
        
        if may_pos <= alice_pos:
            continue
        
        april_pos = birthday_perm.index('april')
        if april_pos < 4:
            continue
        
        sept_pos = birthday_perm.index('sept')
        if sept_pos not in (1, 5):
            continue
        
        mar_pos = birthday_perm.index('mar')
        
        for height_perm in itertools.permutations(heights):
            if height_perm[3] != 'very short':
                continue
            
            if height_perm[bob_pos] != 'tall':
                continue
            
            super_tall_pos = height_perm.index('super tall')
            if abs(super_tall_pos - mar_pos) != 2:
                continue
            
            if height_perm[mar_pos] != 'short':
                continue
            
            for car_perm in itertools.permutations(cars):
                if car_perm[4] != 'ford f150':
                    continue
                
                if car_perm[carol_pos] != 'tesla model 3':
                    continue
                
                if car_perm[2] == 'bmw 3 series':
                    continue
                
                very_tall_pos = height_perm.index('very tall')
                if car_perm[very_tall_pos] != 'toyota camry':
                    continue
                
                if car_perm[mar_pos] != 'honda civic':
                    continue
                
                if carol_pos >= bob_pos:
                    continue
                
                bmw_pos = car_perm.index('bmw 3 series')
                if alice_pos + 1 != bmw_pos:
                    continue
                
                if bmw_pos == 2:
                    continue
                
                for food_perm in itertools.permutations(foods):
                    if food_perm[2] == 'stew':
                        continue
                    
                    if food_perm[eric_pos - 1] != 'soup':
                        continue
                    
                    stir_fry_pos = food_perm.index('stir fry')
                    if stir_fry_pos >= eric_pos:
                        continue
                    
                    pizza_pos = food_perm.index('pizza')
                    if abs(stir_fry_pos - pizza_pos) != 3:
                        continue
                    
                    if pizza_pos != peter_pos + 1:
                        continue
                    
                    spaghetti_pos = food_perm.index('spaghetti')
                    may_pos_b = birthday_perm.index('may')
                    if abs(spaghetti_pos - may_pos_b) != 1:
                        continue
                    
                    solution_rows = []
                    for i in range(6):
                        house_num = str(i + 1)
                        solution_rows.append([
                            house_num,
                            name_perm[i],
                            birthday_perm[i],
                            food_perm[i],
                            height_perm[i],
                            car_perm[i]
                        ])
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
                            "rows": solution_rows
                        }
                    }
                    
                    print(json.dumps(solution, indent=2))
                    exit()