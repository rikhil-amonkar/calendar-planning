import itertools
import json

def main():
    # Define options for each category
    names_options = ['Arnold', 'Eric']
    education_options = ['associate', 'high school']
    height_options = ['short', 'very short']
    food_options = ['grilled cheese', 'pizza']
    drink_options = ['tea', 'water']

    def get_category_values(options, choice):
        if choice == 0:
            h1 = options[0]
            h2 = options[1]
        else:
            h1 = options[1]
            h2 = options[0]
        return (h1, h2)

    def is_valid(house1, house2):
        # Constraint 1: very short → pizza
        for h in [house1, house2]:
            if h['Height'] == 'very short' and h['Food'] != 'pizza':
                return False
        # Constraint 2: grilled cheese in house 2
        if house2['Food'] != 'grilled cheese':
            return False
        # Constraint 3: high school → pizza
        for h in [house1, house2]:
            if h['Education'] == 'high school' and h['Food'] != 'pizza':
                return False
        # Constraint 4: grilled cheese → tea
        for h in [house1, house2]:
            if h['Food'] == 'grilled cheese' and h['Drink'] != 'tea':
                return False
        # Constraint 5: Arnold is pizza lover
        for h in [house1, house2]:
            if h['Food'] == 'pizza' and h['Name'] != 'Arnold':
                return False
        return True

    # Iterate through all possible combinations of choices
    for choices in itertools.product([0, 1], repeat=5):
        n_choice, e_choice, h_choice, f_choice, d_choice = choices

        # Get values for each category
        n_h1, n_h2 = get_category_values(names_options, n_choice)
        e_h1, e_h2 = get_category_values(education_options, e_choice)
        h_h1, h_h2 = get_category_values(height_options, h_choice)
        f_h1, f_h2 = get_category_values(food_options, f_choice)
        d_h1, d_h2 = get_category_values(drink_options, d_choice)

        # Build house data
        house1 = {
            'Name': n_h1,
            'Education': e_h1,
            'Height': h_h1,
            'Food': f_h1,
            'Drink': d_h1,
        }
        house2 = {
            'Name': n_h2,
            'Education': e_h2,
            'Height': h_h2,
            'Food': f_h2,
            'Drink': d_h2,
        }

        if is_valid(house1, house2):
            # Construct the JSON output
            rows = [
                ["1", house1['Name'], house1['Education'], house1['Height'], house1['Food'], house1['Drink']],
                ["2", house2['Name'], house2['Education'], house2['Height'], house2['Food'], house2['Drink']],
            ]
            solution = {
                "solution": {
                    "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                    "rows": rows
                }
            }
            print(json.dumps(solution))
            return

if __name__ == "__main__":
    main()