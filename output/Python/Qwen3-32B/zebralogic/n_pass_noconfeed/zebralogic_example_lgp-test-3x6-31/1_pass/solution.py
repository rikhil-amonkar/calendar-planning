import itertools
import json

# Define the possible values for each category
names = ['Eric', 'Peter', 'Arnold']
drinks = ['milk', 'water', 'tea']
vacations = ['mountain', 'city', 'beach']
houseStyles = ['colonial', 'victorian', 'ranch']
animals = ['cat', 'bird', 'horse']
birthdays = ['jan', 'sept', 'april']

# Generate all permutations for each category
name_perms = list(itertools.permutations(names))
drink_perms = list(itertools.permutations(drinks))
vacation_perms = list(itertools.permutations(vacations))
housestyle_perms = list(itertools.permutations(houseStyles))
animal_perms = list(itertools.permutations(animals))
birthday_perms = list(itertools.permutations(birthdays))

# Iterate through all possible combinations of permutations
for names_p in name_perms:
    for drinks_p in drink_perms:
        for vacations_p in vacation_perms:
            for housestyles_p in housestyle_perms:
                for animals_p in animal_perms:
                    for birthdays_p in birthday_perms:
                        # Check if current combination is valid
                        valid = True
                        
                        # Check per-house constraints
                        
                        # Clue 9: Eric drinks water
                        eric_i = None
                        for i in range(3):
                            if names_p[i] == 'Eric':
                                eric_i = i
                                break
                        if eric_i is None:
                            valid = False
                        else:
                            if drinks_p[eric_i] != 'water':
                                valid = False
                            # Clue 4: water -> mountain vacation
                            if vacations_p[eric_i] != 'mountain':
                                valid = False
                            # Clue 8: mountain vacation -> birthday april
                            if birthdays_p[eric_i] != 'april':
                                valid = False
                        
                        # Clue 5: horse -> Peter
                        if valid:
                            horse_i = None
                            for i in range(3):
                                if animals_p[i] == 'horse':
                                    horse_i = i
                                    break
                            if horse_i is None:
                                valid = False
                            else:
                                if names_p[horse_i] != 'Peter':
                                    valid = False
                        
                        # Clue 7: Peter's vacation is city
                        if valid:
                            peter_i = None
                            for i in range(3):
                                if names_p[i] == 'Peter':
                                    peter_i = i
                                    break
                            if peter_i is None:
                                valid = False
                            else:
                                if vacations_p[peter_i] != 'city':
                                    valid = False
                        
                        # Check positional constraints
                        
                        # Clue 1: colonial is left of milk
                        if valid:
                            colonial_index = housestyles_p.index('colonial')
                            milk_index = drinks_p.index('milk')
                            if colonial_index >= milk_index:
                                valid = False
                        
                        # Clue 2: city is directly left of victorian
                        if valid:
                            try:
                                city_index = vacations_p.index('city')
                                if city_index + 1 >= 3 or housestyles_p[city_index + 1] != 'victorian':
                                    valid = False
                            except ValueError:
                                valid = False
                        
                        # Clue 3: jan is directly left of cat
                        if valid:
                            try:
                                jan_index = birthdays_p.index('jan')
                                if jan_index + 1 >= 3 or animals_p[jan_index + 1] != 'cat':
                                    valid = False
                            except ValueError:
                                valid = False
                        
                        # Clue 6: victorian is right of beach
                        if valid:
                            victorian_index = housestyles_p.index('victorian')
                            beach_index = vacations_p.index('beach')
                            if victorian_index <= beach_index:
                                valid = False
                        
                        if valid:
                            # Found the solution!
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                                    "rows": []
                                }
                            }
                            for i in range(3):
                                house_num = str(i + 1)
                                row = [
                                    house_num,
                                    names_p[i],
                                    drinks_p[i],
                                    vacations_p[i],
                                    housestyles_p[i],
                                    animals_p[i],
                                    birthdays_p[i]
                                ]
                                solution["solution"]["rows"].append(row)
                            print(json.dumps(solution, indent=2))
                            exit()