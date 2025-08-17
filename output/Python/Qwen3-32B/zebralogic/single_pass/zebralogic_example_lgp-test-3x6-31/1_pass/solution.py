import itertools
import json

# Define the categories
names_list = ['Eric', 'Peter', 'Arnold']
drinks_list = ['milk', 'water', 'tea']
vacations_list = ['mountain', 'city', 'beach']
housestyles_list = ['colonial', 'victorian', 'ranch']
animals_list = ['cat', 'bird', 'horse']
birthdays_list = ['jan', 'sept', 'april']

found = False

for names in itertools.permutations(names_list):
    for drinks in itertools.permutations(drinks_list):
        for vacations in itertools.permutations(vacations_list):
            for housestyles in itertools.permutations(housestyles_list):
                for animals in itertools.permutations(animals_list):
                    for birthdays in itertools.permutations(birthdays_list):
                        # Check Clue 9: Eric drinks water
                        e_pos = names.index('Eric')
                        if drinks[e_pos] != 'water':
                            continue
                        # Check Clue 4: Water drinker likes mountain
                        w_pos = drinks.index('water')
                        if vacations[w_pos] != 'mountain':
                            continue
                        # Check Clue 8: Mountain vacation's birthday is April
                        v_mountain_pos = vacations.index('mountain')
                        if birthdays[v_mountain_pos] != 'april':
                            continue
                        # Check Clue 5: Peter has horse
                        p_pos = names.index('Peter')
                        if animals[p_pos] != 'horse':
                            continue
                        # Check Clue 7: Peter's vacation is city
                        if vacations[p_pos] != 'city':
                            continue
                        # Check Clue 2: City vacation directly left of Victorian
                        v_city_pos = vacations.index('city')
                        h_vic_pos = housestyles.index('victorian')
                        if v_city_pos != h_vic_pos - 1:
                            continue
                        # Check Clue 1: Colonial is left of milk
                        c_pos = housestyles.index('colonial')
                        m_pos = drinks.index('milk')
                        if c_pos >= m_pos:
                            continue
                        # Check Clue 3: Jan birthday directly left of cat
                        b_jan_pos = birthdays.index('jan')
                        if b_jan_pos + 1 >= 3 or animals[b_jan_pos + 1] != 'cat':
                            continue
                        # Check Clue 6: Victorian is right of beach vacation
                        h_vic_pos = housestyles.index('victorian')
                        v_beach_pos = vacations.index('beach')
                        if h_vic_pos <= v_beach_pos:
                            continue
                        
                        # Build solution
                        solution_rows = []
                        for i in range(3):
                            house_num = str(i + 1)
                            solution_rows.append([
                                house_num,
                                names[i],
                                drinks[i],
                                vacations[i],
                                housestyles[i],
                                animals[i],
                                birthdays[i]
                            ])
                        
                        # Output JSON
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                                "rows": solution_rows
                            }
                        }
                        print(json.dumps(solution, indent=2))
                        found = True
                        break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if found:
            break
    if found:
        break