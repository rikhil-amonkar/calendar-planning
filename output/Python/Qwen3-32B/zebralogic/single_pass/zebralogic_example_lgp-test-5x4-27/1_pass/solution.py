import itertools
import json

# Define the categories
names_list = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
birthdays_list = ['april', 'feb', 'mar', 'jan', 'sept']
cigars_list = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
drinks_list = ['water', 'coffee', 'tea', 'milk', 'root beer']

# Generate permutations with fixed positions
name_perms = []
for p in itertools.permutations(['Peter', 'Alice', 'Bob', 'Arnold']):
    temp = list(p)
    temp.insert(2, 'Eric')  # house 3 (index 2) is Eric
    name_perms.append(temp)

cigar_perms = []
for p in itertools.permutations(['prince', 'dunhill', 'blends', 'blue master']):
    temp = list(p)
    temp.insert(2, 'pall mall')  # house 3's cigar is pall mall
    cigar_perms.append(temp)

birthday_perms = []
for p in itertools.permutations(['april', 'mar', 'jan', 'sept']):
    temp = list(p)
    temp.insert(1, 'feb')  # house 2's birthday is feb
    birthday_perms.append(temp)

drink_perms = []
for p in itertools.permutations(['water', 'coffee', 'tea', 'milk']):
    temp = list(p)
    temp.insert(2, 'root beer')  # house 3's drink is root beer
    drink_perms.append(temp)

# Now iterate through all combinations
for names in name_perms:
    for cigars in cigar_perms:
        for birthdays in birthday_perms:
            for drinks in drink_perms:
                # Clue 3: Bob's birthday is april
                bob_index = names.index('Bob')
                if birthdays[bob_index] != 'april':
                    continue

                # Clue 4: Dunhill smoker has birthday mar
                dunhill_index = cigars.index('dunhill')
                if birthdays[dunhill_index] != 'mar':
                    continue

                # Clue 5: Peter is to the right of root beer lover (Eric, house 3)
                peter_index = names.index('Peter')
                if peter_index <= 2:  # since house 3 is index 2
                    continue

                # Clue 6: one house between jan and Peter
                jan_index = birthdays.index('jan')
                if abs(peter_index - jan_index) != 2:
                    continue

                # Clue 7: Blends smoker has birthday feb (already handled by birthday_perms)
                blends_index = cigars.index('blends')
                if blends_index != 1:
                    continue

                # Clue 9: Arnold is directly left of Peter
                arnold_index = names.index('Arnold')
                if peter_index != arnold_index + 1:
                    continue

                # Clue 10: milk not in house 5 (index 4)
                if drinks[4] == 'milk':
                    continue

                # Clue 11: Blue Master smoker drinks coffee
                blue_master_index = cigars.index('blue master')
                if drinks[blue_master_index] != 'coffee':
                    continue

                # Clue 12: one house between tea and coffee
                tea_index = drinks.index('tea')
                coffee_index = drinks.index('coffee')
                if abs(tea_index - coffee_index) != 2:
                    continue

                # All constraints are satisfied
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                        "rows": []
                    }
                }
                for i in range(5):
                    house_num = str(i+1)
                    name = names[i]
                    birthday = birthdays[i]
                    cigar = cigars[i]
                    drink = drinks[i]
                    solution["solution"]["rows"].append([house_num, name, birthday, cigar, drink])
                print(json.dumps(solution))
                exit()