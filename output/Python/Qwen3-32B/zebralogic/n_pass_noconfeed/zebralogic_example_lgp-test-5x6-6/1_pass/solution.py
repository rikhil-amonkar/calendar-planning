import itertools
import json

# Define all possible values for each category
names_values = ['Arnold', 'Eric', 'Alice', 'Bob', 'Peter']
vacations_values = ['mountain', 'city', 'cruise', 'beach', 'camping']
education_values = ['doctorate', 'high school', 'bachelor', 'associate', 'master']
colors_values = ['blue', 'red', 'white', 'yellow', 'green']
phones_values = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50', 'samsung galaxy s21']
foods_values = ['grilled cheese', 'stir fry', 'pizza', 'spaghetti', 'stew']

# Generate all valid education permutations
valid_edu = []
for p in itertools.permutations(['high school', 'bachelor', 'associate', 'master']):
    edu = list(p)
    edu.insert(2, 'doctorate')  # house 3 (index 2) is doctorate
    # Check if high school is in position 0 or 4 (clue 13)
    if edu[0] != 'high school' and edu[4] != 'high school':
        continue
    # Check if bachelor and associate are separated by 3 (clue 2)
    b_index = edu.index('bachelor')
    a_index = edu.index('associate')
    if abs(b_index - a_index) != 3:
        continue
    valid_edu.append(edu)

# Now, for each valid education, generate color permutations
for edu in valid_edu:
    b_index = edu.index('bachelor')
    # Determine possible positions for red (clue 18)
    possible_red_positions = []
    if b_index + 3 < 5:
        possible_red_positions.append(b_index + 3)
    if b_index - 3 >= 0:
        possible_red_positions.append(b_index - 3)
    for red_pos in possible_red_positions:
        # Generate color permutations with 'red' at red_pos and green not in position 1 (clue 20)
        remaining_colors = [c for c in colors_values if c != 'red']
        for color_p in itertools.permutations(remaining_colors):
            colors = list(color_p)
            colors.insert(red_pos, 'red')
            # Check clue 20: green not in position 1
            if colors[1] == 'green':
                continue
            # Proceed to generate other permutations
            # Now, generate names permutations with 'Eric' at index 2
            remaining_names = [n for n in names_values if n != 'Eric']
            for names_p in itertools.permutations(remaining_names):
                names = list(names_p)
                names.insert(2, 'Eric')  # house 3 is Eric
                # Now, generate phones permutations with 'samsung galaxy s21' at index 2
                remaining_phones = [p for p in phones_values if p != 'samsung galaxy s21']
                for phones_p in itertools.permutations(remaining_phones):
                    phones = list(phones_p)
                    phones.insert(2, 'samsung galaxy s21')
                    # Now, generate foods permutations with 'pizza' at index 2
                    remaining_foods = [f for f in foods_values if f != 'pizza']
                    for foods_p in itertools.permutations(remaining_foods):
                        foods = list(foods_p)
                        foods.insert(2, 'pizza')
                        # Now, generate vacations permutations
                        for vacations_p in itertools.permutations(vacations_values):
                            # Now, check all constraints
                            # Clue 1: stew not in first house (index 0)
                            if foods[0] == 'stew':
                                continue
                            # Clue 8: stir fry is at the bachelor's index, which is already set
                            if foods[b_index] != 'stir fry':
                                continue
                            # Clue 3: vacation[b_index] is 'mountain'
                            if vacations_p[b_index] != 'mountain':
                                continue
                            # Clue 12: Alice's vacation is 'cruise'
                            try:
                                alice_index = names.index('Alice')
                            except ValueError:
                                continue
                            if vacations_p[alice_index] != 'cruise':
                                continue
                            # Clue 11: camping vacation uses iphone 13
                            try:
                                camping_index = vacations_p.index('camping')
                            except ValueError:
                                continue
                            if phones[camping_index] != 'iphone 13':
                                continue
                            # Clue 22: one house between camping and yellow
                            try:
                                yellow_index = colors.index('yellow')
                            except ValueError:
                                continue
                            if abs(camping_index - yellow_index) != 2:
                                continue
                            # Clue 14: google pixel 6 is Arnold
                            try:
                                google_pixel_index = phones.index('google pixel 6')
                            except ValueError:
                                continue
                            if names[google_pixel_index] != 'Arnold':
                                continue
                            # Clue 16: Arnold's food is grilled cheese
                            arnold_index = names.index('Arnold')
                            if foods[arnold_index] != 'grilled cheese':
                                continue
                            # Clue 17: grilled cheese not in house 4 (index 3)
                            if arnold_index == 3:
                                continue
                            # Clue 15: oneplus 9 is to the right of huawei p50
                            try:
                                oneplus_index = phones.index('oneplus 9')
                                huawei_index = phones.index('huawei p50')
                            except ValueError:
                                continue
                            if oneplus_index <= huawei_index:
                                continue
                            # Clue 10: green is to the right of Peter
                            try:
                                peter_index = names.index('Peter')
                                green_index = colors.index('green')
                            except ValueError:
                                continue
                            if green_index <= peter_index:
                                continue
                            # Clue 21: blue is to the right of Peter
                            try:
                                blue_index = colors.index('blue')
                            except ValueError:
                                continue
                            if blue_index <= peter_index:
                                continue
                            # Clue 19: beach is to the right of city
                            try:
                                beach_index = vacations_p.index('beach')
                                city_index = vacations_p.index('city')
                            except ValueError:
                                continue
                            if beach_index <= city_index:
                                continue
                            # If all constraints are satisfied, this is the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                                    "rows": []
                                }
                            }
                            for i in range(5):
                                house = str(i+1)
                                name = names[i]
                                vacation = vacations_p[i]
                                education = edu[i]
                                color = colors[i]
                                phone = phones[i]
                                food = foods[i]
                                solution["solution"]["rows"].append([house, name, vacation, education, color, phone, food])
                            # Output the JSON
                            print(json.dumps(solution))
                            exit()