from z3 import *
import json

def main():
    # Define the enumerations for each attribute
    Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    Education, (associate, high_school) = EnumSort('Education', ['associate', 'high school'])
    Height, (short, very_short) = EnumSort('Height', ['short', 'very short'])
    Food, (grilled_cheese, pizza) = EnumSort('Food', ['grilled cheese', 'pizza'])
    Drink, (tea, water) = EnumSort('Drink', ['tea', 'water'])

    # Create variables for house 1
    h1_name = Const('h1_name', Name)
    h1_edu = Const('h1_edu', Education)
    h1_ht = Const('h1_ht', Height)
    h1_food = Const('h1_food', Food)
    h1_drink = Const('h1_drink', Drink)

    # Create variables for house 2
    h2_name = Const('h2_name', Name)
    h2_edu = Const('h2_edu', Education)
    h2_ht = Const('h2_ht', Height)
    h2_food = Const('h2_food', Food)
    h2_drink = Const('h2_drink', Drink)

    s = Solver()

    # Each attribute is unique across houses
    s.add(Distinct([h1_name, h2_name]))
    s.add(Distinct([h1_edu, h2_edu]))
    s.add(Distinct([h1_ht, h2_ht]))
    s.add(Distinct([h1_food, h2_food]))
    s.add(Distinct([h1_drink, h2_drink]))

    # Clue 1: The very short person is the pizza lover (equivalence per house)
    s.add((h1_ht == very_short) == (h1_food == pizza))
    s.add((h2_ht == very_short) == (h2_food == pizza))

    # Clue 2: Grilled cheese lover is in house 2
    s.add(h2_food == grilled_cheese)

    # Clue 3: High school diploma holder is the pizza lover (equivalence per house)
    s.add((h1_edu == high_school) == (h1_food == pizza))
    s.add((h2_edu == high_school) == (h2_food == pizza))

    # Clue 4: Tea drinker is the grilled cheese lover (equivalence per house)
    s.add((h1_drink == tea) == (h1_food == grilled_cheese))
    s.add((h2_drink == tea) == (h2_food == grilled_cheese))

    # Clue 5: Arnold is the pizza lover (equivalence per house)
    s.add((h1_name == Arnold) == (h1_food == pizza))
    s.add((h2_name == Arnold) == (h2_food == pizza))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Retrieve values as strings
        h1_row = [
            "1",
            str(m.eval(h1_name)),
            str(m.eval(h1_edu)),
            str(m.eval(h1_ht)),
            str(m.eval(h1_food)),
            str(m.eval(h1_drink))
        ]
        h2_row = [
            "2",
            str(m.eval(h2_name)),
            str(m.eval(h2_edu)),
            str(m.eval(h2_ht)),
            str(m.eval(h2_food)),
            str(m.eval(h2_drink))
        ]
        
        # Construct the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                "rows": [h1_row, h2_row]
            }
        }
        # Output as JSON
        print(json.dumps(solution_dict))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()