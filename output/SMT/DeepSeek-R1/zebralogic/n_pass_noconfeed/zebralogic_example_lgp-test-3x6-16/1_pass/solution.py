import json
from z3 import *

def main():
    # Initialize the solver
    s = Solver()

    # Define the attributes with integer mappings
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['tea', 'water', 'milk']
    nationalities = ['dane', 'brit', 'swede']
    educations = ['high school', 'associate', 'bachelor']
    house_styles = ['victorian', 'colonial', 'ranch']
    smoothies = ['cherry', 'watermelon', 'desert']

    # Create Z3 variables for each attribute per house
    name = [Int(f'name_{i}') for i in range(1,4)]
    drink = [Int(f'drink_{i}') for i in range(1,4)]
    nationality = [Int(f'nationality_{i}') for i in range(1,4)]
    education = [Int(f'education_{i}') for i in range(1,4)]
    house_style = [Int(f'house_style_{i}') for i in range(1,4)]
    smoothie = [Int(f'smoothie_{i}') for i in range(1,4)]

    # Add constraints that each attribute is one of the possible values (0,1,2)
    for i in range(3):
        s.add(name[i] >= 0, name[i] <= 2)
        s.add(drink[i] >= 0, drink[i] <= 2)
        s.add(nationality[i] >= 0, nationality[i] <= 2)
        s.add(education[i] >= 0, education[i] <= 2)
        s.add(house_style[i] >= 0, house_style[i] <= 2)
        s.add(smoothie[i] >= 0, smoothie[i] <= 2)

    # Each attribute set must have distinct values
    s.add(Distinct(name))
    s.add(Distinct(drink))
    s.add(Distinct(nationality))
    s.add(Distinct(education))
    s.add(Distinct(house_style))
    s.add(Distinct(smoothie))

    # Clue 1: One house between Eric and tea drinker
    # Eric is name index 0, tea is drink index 0
    s.add(Or(
        And(name[0] == 0, drink[2] == 0),  # Eric in 1, tea in 3
        And(name[2] == 0, drink[0] == 0)   # Eric in 3, tea in 1
    ))

    # Clue 2: Milk drinker is in ranch-style home
    # Milk is drink index 2, ranch is house_style index 2
    for i in range(3):
        s.add(Implies(drink[i] == 2, house_style[i] == 2))

    # Clue 3: Bachelor's degree in second house
    # Bachelor is education index 2
    s.add(education[1] == 2)

    # Clue 4: High school diploma is Dane
    # High school is education index 0, Dane is nationality index 0
    for i in range(3):
        s.add(Implies(education[i] == 0, nationality[i] == 0))

    # Clue 5: Desert smoothie is Swedish person
    # Desert smoothie is smoothie index 2, Swede is nationality index 2
    for i in range(3):
        s.add(Implies(smoothie[i] == 2, nationality[i] == 2))

    # Clue 6: Victorian house not in first house
    # Victorian is house_style index 0
    s.add(house_style[0] != 0)

    # Clue 7: Cherry smoothie is colonial-style house
    # Cherry smoothie is smoothie index 0, colonial is house_style index 1
    for i in range(3):
        s.add(Implies(smoothie[i] == 0, house_style[i] == 1))

    # Clue 8: Arnold is right of Victorian house
    # Arnold is name index 2
    victorian_pos = Int('victorian_pos')
    arnold_pos = Int('arnold_pos')
    s.add(victorian_pos >= 1, victorian_pos <= 3)
    s.add(arnold_pos >= 1, arnold_pos <= 3)
    for i in range(3):
        s.add(Implies(house_style[i] == 0, victorian_pos == i+1))
        s.add(Implies(name[i] == 2, arnold_pos == i+1))
    s.add(arnold_pos > victorian_pos)

    # Clue 9: Ranch-style home has high school diploma
    # Ranch is house_style index 2, high school is education index 0
    for i in range(3):
        s.add(Implies(house_style[i] == 2, education[i] == 0))

    # Check if the problem is satisfied
    if s.check() == sat:
        model = s.model()
        result = []
        for i in range(3):
            house_num = str(i+1)
            n = model.evaluate(name[i]).as_long()
            d = model.evaluate(drink[i]).as_long()
            nat = model.evaluate(nationality[i]).as_long()
            edu = model.evaluate(education[i]).as_long()
            hs = model.evaluate(house_style[i]).as_long()
            sm = model.evaluate(smoothie[i]).as_long()
            row = [house_num, names[n], drinks[d], nationalities[nat], educations[edu], house_styles[hs], smoothies[sm]]
            result.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                "rows": result
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()