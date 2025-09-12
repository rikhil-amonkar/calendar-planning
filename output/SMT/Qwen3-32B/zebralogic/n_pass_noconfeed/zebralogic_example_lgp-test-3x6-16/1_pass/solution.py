from z3 import *

def main():
    # Define EnumSorts for each attribute
    Name, (Eric, Peter, Arnold) = EnumSort('Name', ['Eric', 'Peter', 'Arnold'])
    Drink, (Tea, Water, Milk) = EnumSort('Drink', ['tea', 'water', 'milk'])
    Nationality, (Dane, Brit, Swede) = EnumSort('Nationality', ['dane', 'brit', 'swede'])
    Education, (HighSchool, Associate, Bachelor) = EnumSort('Education', ['high_school', 'associate', 'bachelor'])
    HouseStyle, (Victorian, Colonial, Ranch) = EnumSort('HouseStyle', ['victorian', 'colonial', 'ranch'])
    Smoothie, (Cherry, Watermelon, Desert) = EnumSort('Smoothie', ['cherry', 'watermelon', 'desert'])

    # Create variables for each house (1, 2, 3)
    name = [Const(f"name_{i}", Name) for i in range(1, 4)]
    drink = [Const(f"drink_{i}", Drink) for i in range(1, 4)]
    nationality = [Const(f"nationality_{i}", Nationality) for i in range(1, 4)]
    education = [Const(f"education_{i}", Education) for i in range(1, 4)]
    housestyle = [Const(f"housestyle_{i}", HouseStyle) for i in range(1, 4)]
    smoothie = [Const(f"smoothie_{i}", Smoothie) for i in range(1, 4)]

    s = Solver()

    # Add constraints for uniqueness in each attribute
    for attr in [name, drink, nationality, education, housestyle, smoothie]:
        for i in range(3):
            for j in range(i+1, 3):
                s.add(attr[i] != attr[j])

    # Add constraints for the clues
    # Clue 1: There is one house between Eric and the tea drinker.
    E_house = If(name[0] == Eric, 1, If(name[1] == Eric, 2, 3))
    T_house = If(drink[0] == Tea, 1, If(drink[1] == Tea, 2, 3))
    s.add(Abs(E_house - T_house) == 2)

    # Clue 2: Milk drinker is in ranch-style home.
    for i in range(3):
        s.add(Implies(drink[i] == Milk, housestyle[i] == Ranch))

    # Clue 3: Bachelor's degree is in the second house.
    s.add(education[1] == Bachelor)

    # Clue 4: High school diploma is Dane.
    for i in range(3):
        s.add(Implies(education[i] == HighSchool, nationality[i] == Dane))

    # Clue 5: Desert smoothie lover is the Swedish person.
    for i in range(3):
        s.add(Implies(smoothie[i] == Desert, nationality[i] == Swede))

    # Clue 6: The person residing in a Victorian house is not in the first house.
    s.add(housestyle[0] != Victorian)

    # Clue 7: Cherry smoothie lover is in colonial-style house.
    for i in range(3):
        s.add(Implies(smoothie[i] == Cherry, housestyle[i] == Colonial))

    # Clue 8: Arnold is somewhere to the right of the person residing in a Victorian house.
    A_house = If(name[0] == Arnold, 1, If(name[1] == Arnold, 2, 3))
    V_house = If(housestyle[0] == Victorian, 1, If(housestyle[1] == Victorian, 2, 3))
    s.add(A_house > V_house)

    # Clue 9: The person in a ranch-style home is the person with a high school diploma.
    for i in range(3):
        s.add(Implies(housestyle[i] == Ranch, education[i] == HighSchool))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()

        # Mapping Enum constants to desired output strings
        name_map = {Eric: 'Eric', Peter: 'Peter', Arnold: 'Arnold'}
        drink_map = {Tea: 'tea', Water: 'water', Milk: 'milk'}
        nationality_map = {Dane: 'dane', Brit: 'brit', Swede: 'swede'}
        education_map = {HighSchool: 'high school', Associate: 'associate', Bachelor: 'bachelor'}
        housestyle_map = {Victorian: 'victorian', Colonial: 'colonial', Ranch: 'ranch'}
        smoothie_map = {Cherry: 'cherry', Watermelon: 'watermelon', Desert: 'desert'}

        # Extract the solution
        rows = []
        for i in range(3):
            house_num = i + 1
            n = name_map[model[name[i]]]
            d = drink_map[model[drink[i]]]
            nat = nationality_map[model[nationality[i]]]
            ed = education_map[model[education[i]]]
            hs = housestyle_map[model[housestyle[i]]]
            sm = smoothie_map[model[smoothie[i]]]
            rows.append([str(house_num), n, d, nat, ed, hs, sm])

        solution = {
            "solution": {
                "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                "rows": rows
            }
        }

        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()