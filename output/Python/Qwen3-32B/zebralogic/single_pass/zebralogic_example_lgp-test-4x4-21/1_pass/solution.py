import itertools
import json

names_list = ['Eric', 'Peter', 'Alice', 'Arnold']
cars_list = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
birthdays_list = ['jan', 'april', 'sept', 'feb']
hobbies_list = ['painting', 'cooking', 'gardening', 'photography']

for names in itertools.permutations(names_list):
    for cars in itertools.permutations(cars_list):
        # Check clue 8: Peter's car is Toyota Camry
        peter_idx = names.index('Peter')
        if cars[peter_idx] != 'toyota camry':
            continue
        # Check clue 6: Arnold's car is Tesla
        arnold_idx = names.index('Arnold')
        if cars[arnold_idx] != 'tesla model 3':
            continue
        # Check clue 4: Honda directly left of Tesla (i.e., at arnold_idx - 1)
        if arnold_idx == 0:
            continue  # No house to the left
        if cars[arnold_idx - 1] != 'honda civic':
            continue
        for birthdays in itertools.permutations(birthdays_list):
            # Check clue 9: Arnold's birthday is april
            if birthdays[arnold_idx] != 'april':
                continue
            # Check clue 11: Peter's birthday is jan
            if birthdays[peter_idx] != 'jan':
                continue
            # Check clue 1: jan is not in house 2 (index 1)
            jan_pos = birthdays.index('jan')
            if jan_pos == 1:
                continue
            for hobbies in itertools.permutations(hobbies_list):
                # Check clue 10: Alice's hobby is photography
                alice_idx = names.index('Alice')
                if hobbies[alice_idx] != 'photography':
                    continue
                # Check clue 7: birthday feb's hobby is cooking
                feb_pos = birthdays.index('feb')
                if hobbies[feb_pos] != 'cooking':
                    continue
                # Check clue 2 and 3: photography is left of Eric and Peter
                photo_pos = hobbies.index('photography')
                eric_idx = names.index('Eric')
                peter_idx = names.index('Peter')
                if photo_pos >= eric_idx or photo_pos >= peter_idx:
                    continue
                # Check clue 5: Tesla (arnold_idx) and gardening
                gardening_pos = hobbies.index('gardening')
                if abs(gardening_pos - arnold_idx) != 2:
                    continue
                # If all constraints are met, build the solution
                rows = []
                for i in range(4):
                    house_num = str(i + 1)
                    name = names[i]
                    car = cars[i]
                    birthday = birthdays[i]
                    hobby = hobbies[i]
                    rows.append([house_num, name, car, birthday, hobby])
                solution = {
                    "solution": {
                        "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                        "rows": rows
                    }
                }
                print(json.dumps(solution, indent=2))
                exit()