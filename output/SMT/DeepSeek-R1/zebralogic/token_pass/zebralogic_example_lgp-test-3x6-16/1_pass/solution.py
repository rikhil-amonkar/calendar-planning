import json
from z3 import *

def main():
    # Create the solver
    s = Solver()

    # Define the attributes with EnumSort
    Name = Datatype('Name')
    Name.declare('Eric')
    Name.declare('Peter')
    Name.declare('Arnold')
    Name = Name.create()

    Drink = Datatype('Drink')
    Drink.declare('tea')
    Drink.declare('water')
    Drink.declare('milk')
    Drink = Drink.create()

    Nationality = Datatype('Nationality')
    Nationality.declare('dane')
    Nationality.declare('brit')
    Nationality.declare('swede')
    Nationality = Nationality.create()

    Education = Datatype('Education')
    Education.declare('high_school')
    Education.declare('associate')
    Education.declare('bachelor')
    Education = Education.create()

    HouseStyle = Datatype('HouseStyle')
    HouseStyle.declare('victorian')
    HouseStyle.declare('colonial')
    HouseStyle.declare('ranch')
    HouseStyle = HouseStyle.create()

    Smoothie = Datatype('Smoothie')
    Smoothie.declare('cherry')
    Smoothie.declare('watermelon')
    Smoothie.declare('desert')
    Smoothie = Smoothie.create()

    # Create variables for each house and each attribute
    names = [Const(f'name_{i}', Name) for i in range(3)]
    drinks = [Const(f'drink_{i}', Drink) for i in range(3)]
    nationalities = [Const(f'nationality_{i}', Nationality) for i in range(3)]
    educations = [Const(f'education_{i}', Education) for i in range(3)]
    housestyles = [Const(f'housestyle_{i}', HouseStyle) for i in range(3)]
    smoothies = [Const(f'smoothie_{i}', Smoothie) for i in range(3)]

    # Add constraints that all attributes are distinct
    s.add(Distinct(names))
    s.add(Distinct(drinks))
    s.add(Distinct(nationalities))
    s.add(Distinct(educations))
    s.add(Distinct(housestyles))
    s.add(Distinct(smoothies))

    # Clue 1: One house between Eric and tea drinker
    eric_index = Int('eric_index')
    tea_index = Int('tea_index')
    s.add(eric_index >= 0, eric_index < 3)
    s.add(tea_index >= 0, tea_index < 3)
    s.add(Abs(eric_index - tea_index) == 2)
    for i in range(3):
        s.add(If(names[i] == Name.Eric, eric_index == i, True))
        s.add(If(drinks[i] == Drink.tea, tea_index == i, True))

    # Clue 2: Milk drinker is in ranch house
    for i in range(3):
        s.add(If(drinks[i] == Drink.milk, housestyles[i] == HouseStyle.ranch, True))
        s.add(If(housestyles[i] == HouseStyle.ranch, drinks[i] == Drink.milk, True))

    # Clue 3: Bachelor degree in second house (index 1)
    s.add(educations[1] == Education.bachelor)

    # Clue 4: High school diploma is Dane
    for i in range(3):
        s.add(If(educations[i] == Education.high_school, nationalities[i] == Nationality.dane, True))
        s.add(If(nationalities[i] == Nationality.dane, educations[i] == Education.high_school, True))

    # Clue 5: Desert smoothie is Swede
    for i in range(3):
        s.add(If(smoothies[i] == Smoothie.desert, nationalities[i] == Nationality.swede, True))
        s.add(If(nationalities[i] == Nationality.swede, smoothies[i] == Smoothie.desert, True))

    # Clue 6: Victorian house not in first house (index 0)
    s.add(housestyles[0] != HouseStyle.victorian)

    # Clue 7: Cherry smoothie is colonial house
    for i in range(3):
        s.add(If(smoothies[i] == Smoothie.cherry, housestyles[i] == HouseStyle.colonial, True))
        s.add(If(housestyles[i] == HouseStyle.colonial, smoothies[i] == Smoothie.cherry, True))

    # Clue 8: Arnold is right of Victorian house
    victorian_index = Int('victorian_index')
    arnold_index = Int('arnold_index')
    s.add(victorian_index >= 0, victorian_index < 3)
    s.add(arnold_index >= 0, arnold_index < 3)
    s.add(arnold_index > victorian_index)
    for i in range(3):
        s.add(If(housestyles[i] == HouseStyle.victorian, victorian_index == i, True))
        s.add(If(names[i] == Name.Arnold, arnold_index == i, True))

    # Clue 9: Ranch house has high school diploma
    for i in range(3):
        s.add(If(housestyles[i] == HouseStyle.ranch, educations[i] == Education.high_school, True))
        s.add(If(educations[i] == Education.high_school, housestyles[i] == HouseStyle.ranch, True))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        
        # Map house indices to attribute values
        result = []
        attr_names = ['Name', 'Drink', 'Nationality', 'Education', 'HouseStyle', 'Smoothie']
        for i in range(3):
            name_val = m.eval(names[i])
            drink_val = m.eval(drinks[i])
            nationality_val = m.eval(nationalities[i])
            education_val = m.eval(educations[i])
            housestyle_val = m.eval(housestyles[i])
            smoothie_val = m.eval(smoothies[i])
            
            # Convert Z3 values to strings
            row = [str(i+1)]
            for val in [name_val, drink_val, nationality_val, education_val, housestyle_val, smoothie_val]:
                if val == Name.Eric:
                    row.append('Eric')
                elif val == Name.Peter:
                    row.append('Peter')
                elif val == Name.Arnold:
                    row.append('Arnold')
                elif val == Drink.tea:
                    row.append('tea')
                elif val == Drink.water:
                    row.append('water')
                elif val == Drink.milk:
                    row.append('milk')
                elif val == Nationality.dane:
                    row.append('dane')
                elif val == Nationality.brit:
                    row.append('brit')
                elif val == Nationality.swede:
                    row.append('swede')
                elif val == Education.high_school:
                    row.append('high school')
                elif val == Education.associate:
                    row.append('associate')
                elif val == Education.bachelor:
                    row.append('bachelor')
                elif val == HouseStyle.victorian:
                    row.append('victorian')
                elif val == HouseStyle.colonial:
                    row.append('colonial')
                elif val == HouseStyle.ranch:
                    row.append('ranch')
                elif val == Smoothie.cherry:
                    row.append('cherry')
                elif val == Smoothie.watermelon:
                    row.append('watermelon')
                elif val == Smoothie.desert:
                    row.append('desert')
                else:
                    row.append('unknown')
            result.append(row)
        
        # Format the output JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()