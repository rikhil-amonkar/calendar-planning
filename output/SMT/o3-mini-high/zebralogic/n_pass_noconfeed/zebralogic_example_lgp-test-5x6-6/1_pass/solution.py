from z3 import *
import json

def main():
    s = Solver()

    # Define variables for each attribute category.
    # Names
    Arnold = Int('Arnold')
    Eric = Int('Eric')
    Alice = Int('Alice')
    Bob = Int('Bob')
    Peter = Int('Peter')
    names = {'Arnold': Arnold, 'Eric': Eric, 'Alice': Alice, 'Bob': Bob, 'Peter': Peter}

    # Vacations
    mountain = Int('mountain')
    city = Int('city')
    cruise = Int('cruise')
    beach = Int('beach')
    camping = Int('camping')
    vacations = {'mountain': mountain, 'city': city, 'cruise': cruise, 'beach': beach, 'camping': camping}

    # Education
    doctorate = Int('doctorate')
    high_school = Int('high school')
    bachelor = Int('bachelor')
    associate = Int('associate')
    master = Int('master')
    educations = {'doctorate': doctorate, 'high school': high_school, 'bachelor': bachelor, 'associate': associate, 'master': master}

    # Colors
    blue = Int('blue')
    red = Int('red')
    white = Int('white')
    yellow = Int('yellow')
    green = Int('green')
    colors = {'blue': blue, 'red': red, 'white': white, 'yellow': yellow, 'green': green}

    # Phone Models
    google_pixel6 = Int('google pixel 6')
    iphone13 = Int('iphone 13')
    oneplus9 = Int('oneplus 9')
    huawei_p50 = Int('huawei p50')
    samsung_galaxy_s21 = Int('samsung galaxy s21')
    phones = {'google pixel 6': google_pixel6, 'iphone 13': iphone13, 'oneplus 9': oneplus9,
              'huawei p50': huawei_p50, 'samsung galaxy s21': samsung_galaxy_s21}

    # Foods
    grilled_cheese = Int('grilled cheese')
    stir_fry = Int('stir fry')
    pizza = Int('pizza')
    spaghetti = Int('spaghetti')
    stew = Int('stew')
    foods = {'grilled cheese': grilled_cheese, 'stir fry': stir_fry, 'pizza': pizza, 'spaghetti': spaghetti, 'stew': stew}

    # Add domain constraints for every variable (houses 1 to 5)
    all_vars = list(names.values()) + list(vacations.values()) + list(educations.values()) + \
               list(colors.values()) + list(phones.values()) + list(foods.values())
    for v in all_vars:
        s.add(And(v >= 1, v <= 5))

    # Add distinct constraints for each category.
    s.add(Distinct(list(names.values())))
    s.add(Distinct(list(vacations.values())))
    s.add(Distinct(list(educations.values())))
    s.add(Distinct(list(colors.values())))
    s.add(Distinct(list(phones.values())))
    s.add(Distinct(list(foods.values())))

    # Clue 1: The person who loves the stew is not in the first house.
    s.add(stew != 1)

    # Clue 2: There are two houses between the person who loves stir fry and the person with an associate's degree.
    s.add(Abs(stir_fry - associate) == 3)

    # Clue 3: The person who enjoys mountain retreats is the person with a bachelor's degree.
    s.add(mountain == bachelor)

    # Clue 4: The person with a doctorate is somewhere to the right of Bob.
    s.add(doctorate > Bob)

    # Clue 5: The person who uses a Samsung Galaxy S21 is in the third house.
    s.add(samsung_galaxy_s21 == 3)

    # Clue 6: Eric is the person with a doctorate.
    s.add(Eric == doctorate)

    # Clue 7: The person with a doctorate is in the third house.
    s.add(doctorate == 3)

    # Clue 8: The person who loves stir fry is the person with a bachelor's degree.
    s.add(stir_fry == bachelor)

    # Clue 9: The person with a doctorate is the person who is a pizza lover.
    s.add(pizza == doctorate)

    # Clue 10: The person whose favorite color is green is somewhere to the right of Peter.
    s.add(green > Peter)

    # Clue 11: The person who enjoys camping trips is the person who uses an iPhone 13.
    s.add(camping == iphone13)

    # Clue 12: The person who likes going on cruises is Alice.
    s.add(cruise == Alice)

    # Clue 13: There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
    s.add(Abs(high_school - samsung_galaxy_s21) == 2)

    # Clue 14: The person who uses a Google Pixel 6 is Arnold.
    s.add(google_pixel6 == Arnold)

    # Clue 15: The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
    s.add(oneplus9 > huawei_p50)

    # Clue 16: Arnold is the person who loves eating grilled cheese.
    s.add(grilled_cheese == Arnold)

    # Clue 17: The person who loves eating grilled cheese is not in the fourth house.
    s.add(grilled_cheese != 4)

    # Clue 18: There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
    s.add(Abs(bachelor - red) == 3)

    # Clue 19: The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
    s.add(beach > city)

    # Clue 20: The person whose favorite color is green is not in the second house.
    s.add(green != 2)

    # Clue 21: The person who loves blue is somewhere to the right of Peter.
    s.add(blue > Peter)

    # Clue 22: There is one house between the person who enjoys camping trips and the person who loves yellow.
    s.add(Abs(camping - yellow) == 2)

    # Solve the puzzle
    if s.check() == sat:
        m = s.model()

        # Build a mapping from house number to its attributes.
        solution_by_house = {i: {} for i in range(1, 6)}
        for key, var in names.items():
            solution_by_house[m[var].as_long()]['Name'] = key
        for key, var in vacations.items():
            solution_by_house[m[var].as_long()]['Vacation'] = key
        for key, var in educations.items():
            solution_by_house[m[var].as_long()]['Education'] = key
        for key, var in colors.items():
            solution_by_house[m[var].as_long()]['Color'] = key
        for key, var in phones.items():
            solution_by_house[m[var].as_long()]['PhoneModel'] = key
        for key, var in foods.items():
            solution_by_house[m[var].as_long()]['Food'] = key

        header = ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"]
        rows = []
        for i in range(1, 6):
            row = [
                str(i),
                solution_by_house[i].get('Name', ''),
                solution_by_house[i].get('Vacation', ''),
                solution_by_house[i].get('Education', ''),
                solution_by_house[i].get('Color', ''),
                solution_by_house[i].get('PhoneModel', ''),
                solution_by_house[i].get('Food', '')
            ]
            rows.append(row)

        output = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()