import itertools
import json

names_values = ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter']
birthdays_values = ['feb', 'mar', 'sept', 'jan', 'may', 'april']
foods_values = ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
heights_values = ['very short', 'average', 'super tall', 'short', 'very tall', 'tall']
cars_values = ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic']

height_perms = [p for p in itertools.permutations(heights_values) if p[3] == 'very short']

for height_perm in height_perms:
    s_pos = height_perm.index('short')
    vt_pos = height_perm.index('very tall')
    t_pos = height_perm.index('tall')
    
    for car_perm in itertools.permutations(cars_values):
        if car_perm[4] != 'ford f150':
            continue
        if car_perm[s_pos] != 'honda civic':
            continue
        if car_perm[vt_pos] != 'toyota camry':
            continue
        if car_perm[2] == 'bmw 3 series':
            continue
        
        for name_perm in itertools.permutations(names_values):
            if name_perm[t_pos] != 'Bob':
                continue
            carol_pos = name_perm.index('Carol')
            if car_perm[carol_pos] != 'tesla model 3':
                continue
            alice_pos = name_perm.index('Alice')
            if alice_pos + 1 >= 6 or car_perm[alice_pos + 1] != 'bmw 3 series':
                continue
            peter_pos = name_perm.index('Peter')
            if name_perm.index('Carol') >= t_pos:
                continue
            
            for birthday_perm in itertools.permutations(birthdays_values):
                if birthday_perm[s_pos] != 'mar':
                    continue
                eric_pos = name_perm.index('Eric')
                if birthday_perm[eric_pos] != 'jan':
                    continue
                may_pos = birthday_perm.index('may')
                carol_name_pos_b = name_perm.index('Carol')
                if may_pos >= carol_name_pos_b:
                    continue
                alice_name_pos_b = name_perm.index('Alice')
                if may_pos <= alice_name_pos_b:
                    continue
                april_pos = birthday_perm.index('april')
                if april_pos <= 3:
                    continue
                sept_pos = birthday_perm.index('sept')
                if sept_pos not in [1, 5]:
                    continue
                st_pos = height_perm.index('super tall')
                if abs(s_pos - st_pos) != 2:
                    continue
                
                for food_perm in itertools.permutations(foods_values):
                    if food_perm[2] == 'stew':
                        continue
                    sf_pos = food_perm.index('stir fry')
                    eric_food_pos = name_perm.index('Eric')
                    if sf_pos >= eric_food_pos:
                        continue
                    pizza_pos = food_perm.index('pizza')
                    if abs(sf_pos - pizza_pos) != 3:
                        continue
                    soup_pos = food_perm.index('soup')
                    if soup_pos != eric_food_pos - 1:
                        continue
                    if food_perm[peter_pos + 1] != 'pizza':
                        continue
                    spaghetti_pos = food_perm.index('spaghetti')
                    may_bday_pos = birthday_perm.index('may')
                    if abs(spaghetti_pos - may_bday_pos) != 1:
                        continue
                    
                    # All constraints passed
                    solution_rows = []
                    for i in range(6):
                        house_num = str(i+1)
                        name = name_perm[i]
                        birthday = birthday_perm[i]
                        food = food_perm[i]
                        height = height_perm[i]
                        car = car_perm[i]
                        solution_rows.append([house_num, name, birthday, food, height, car])
                    
                    print(json.dumps({"solution": {"header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"], "rows": solution_rows}}))
                    exit()