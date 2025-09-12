from z3 import *
import json

def main():
    s = Solver()

    # Variables for house 1
    h1_name = String('h1_name')
    h1_education = String('h1_education')
    h1_height = String('h1_height')
    h1_food = String('h1_food')
    h1_drink = String('h1_drink')

    # Variables for house 2
    h2_name = String('h2_name')
    h2_education = String('h2_education')
    h2_height = String('h2_height')
    h2_food = String('h2_food')
    h2_drink = String('h2_drink')

    # Add possible values constraints
    names = ['Arnold', 'Eric']
    educations = ['associate', 'high school']
    heights = ['short', 'very short']
    foods = ['grilled cheese', 'pizza']
    drinks = ['tea', 'water']

    def add_possible_values(var, options):
        s.add(Or([var == opt for opt in options]))

    add_possible_values(h1_name, names)
    add_possible_values(h2_name, names)
    add_possible_values(h1_education, educations)
    add_possible_values(h2_education, educations)
    add_possible_values(h1_height, heights)
    add_possible_values(h2_height, heights)
    add_possible_values(h1_food, foods)
    add_possible_values(h2_food, foods)
    add_possible_values(h1_drink, drinks)
    add_possible_values(h2_drink, drinks)

    # Add uniqueness constraints
    s.add(h1_name != h2_name)
    s.add(h1_education != h2_education)
    s.add(h1_height != h2_height)
    s.add(h1_food != h2_food)
    s.add(h1_drink != h2_drink)

    # Add clues
    # Clue 2: The grilled cheese lover is in the second house.
    s.add(h2_food == 'grilled cheese')

    # Clue 5: Arnold is the pizza lover.
    s.add(If(h1_name == 'Arnold', h1_food == 'pizza', True))
    s.add(If(h2_name == 'Arnold', h2_food == 'pizza', True))

    # Clue 1: very short → pizza
    s.add(If(h1_height == 'very short', h1_food == 'pizza', True))
    s.add(If(h2_height == 'very short', h2_food == 'pizza', True))

    # Clue 3: high school → pizza
    s.add(If(h1_education == 'high school', h1_food == 'pizza', True))
    s.add(If(h2_education == 'high school', h2_food == 'pizza', True))

    # Clue 4: tea → grilled cheese
    s.add(If(h1_drink == 'tea', h1_food == 'grilled cheese', True))
    s.add(If(h2_drink == 'tea', h2_food == 'grilled cheese', True))

    if s.check() == sat:
        m = s.model()
        # Extract values for each house
        def get_val(var):
            return m.eval(var).as_string()
        
        h1 = [get_val(h1_name), get_val(h1_education), get_val(h1_height), get_val(h1_food), get_val(h1_drink)]
        h2 = [get_val(h2_name), get_val(h2_education), get_val(h2_height), get_val(h2_food), get_val(h2_drink)]
        
        # Now, create the JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                "rows": [
                    ["1", h1[0], h1[1], h1[2], h1[3], h1[4]],
                    ["2", h2[0], h2[1], h2[2], h2[3], h2[4]]
                ]
            }
        }
        print(json.dumps(solution))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()