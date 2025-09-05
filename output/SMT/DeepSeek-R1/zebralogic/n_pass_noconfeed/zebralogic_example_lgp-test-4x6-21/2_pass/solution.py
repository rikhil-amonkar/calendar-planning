from z3 import *
import json

def main():
    # Create the solver
    s = Solver()

    # Define the categories and their values
    names = ['Peter', 'Arnold', 'Alice', 'Eric']
    flowers = ['roses', 'daffodils', 'carnations', 'lilies']
    hobbies = ['photography', 'painting', 'cooking', 'gardening']
    pets = ['dog', 'fish', 'bird', 'cat']
    colors = ['red', 'yellow', 'green', 'white']
    house_styles = ['craftsman', 'colonial', 'ranch', 'victorian']

    # Create enums for each category and get their constants
    Name, (Peter, Arnold, Alice, Eric) = EnumSort('Name', names)
    Flower, (roses, daffodils, carnations, lilies) = EnumSort('Flower', flowers)
    Hobby, (photography, painting, cooking, gardening) = EnumSort('Hobby', hobbies)
    Pet, (dog, fish, bird, cat) = EnumSort('Pet', pets)
    Color, (red, yellow, green, white) = EnumSort('Color', colors)
    HouseStyle, (craftsman, colonial, ranch, victorian) = EnumSort('HouseStyle', house_styles)

    # Create arrays for each attribute per house (index 0 = house1, 1 = house2, etc.)
    name = [Const(f'name_{i}', Name) for i in range(4)]
    flower = [Const(f'flower_{i}', Flower) for i in range(4)]
    hobby = [Const(f'hobby_{i}', Hobby) for i in range(4)]
    pet = [Const(f'pet_{i}', Pet) for i in range(4)]
    color = [Const(f'color_{i}', Color) for i in range(4)]
    house_style = [Const(f'house_style_{i}', HouseStyle) for i in range(4)]

    # Each attribute must be distinct
    s.add(Distinct(name))
    s.add(Distinct(flower))
    s.add(Distinct(hobby))
    s.add(Distinct(pet))
    s.add(Distinct(color))
    s.add(Distinct(house_style))

    # Clue 1: The person in a Craftsman-style house is Arnold.
    for i in range(4):
        s.add(Implies(house_style[i] == craftsman, name[i] == Arnold))

    # Clue 2: The person who loves the rose bouquet is somewhere to the right of Peter.
    peter_house = Int('peter_house')
    s.add(And(1 <= peter_house, peter_house <= 4))
    for i in range(4):
        s.add(If(name[i] == Peter, peter_house == i+1, True))

    rose_house = Int('rose_house')
    s.add(And(1 <= rose_house, rose_house <= 4))
    for i in range(4):
        s.add(If(flower[i] == roses, rose_house == i+1, True))

    s.add(rose_house > peter_house)

    # Clue 3: The photography enthusiast is the person who owns a dog.
    for i in range(4):
        s.add(Implies(hobby[i] == photography, pet[i] == dog))

    # Clue 4: The person who loves a bouquet of daffodils is not in the fourth house.
    s.add(flower[3] != daffodils)

    # Clue 5: The person who loves the rose bouquet is the person whose favorite color is red.
    for i in range(4):
        s.add(Implies(flower[i] == roses, color[i] == red))

    # Clue 6: The person in a Craftsman-style house is in the second house.
    s.add(house_style[1] == craftsman)

    # Clue 7: Eric is the person residing in a Victorian house.
    for i in range(4):
        s.add(Implies(name[i] == Eric, house_style[i] == victorian))

    # Clue 8: The person with an aquarium of fish is the person who loves white.
    for i in range(4):
        s.add(Implies(pet[i] == fish, color[i] == white))

    # Clue 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
    red_house = Int('red_house')
    s.add(And(1 <= red_house, red_house <= 4))
    for i in range(4):
        s.add(If(color[i] == red, red_house == i+1, True))

    cooking_house = Int('cooking_house')
    s.add(And(1 <= cooking_house, cooking_house <= 4))
    for i in range(4):
        s.add(If(hobby[i] == cooking, cooking_house == i+1, True))

    s.add(cooking_house > red_house)

    # Clue 10: The person who loves white is the person who loves a carnations arrangement.
    for i in range(4):
        s.add(Implies(color[i] == white, flower[i] == carnations))

    # Clue 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
    white_house = Int('white_house')
    s.add(And(1 <= white_house, white_house <= 4))
    for i in range(4):
        s.add(If(color[i] == white, white_house == i+1, True))

    gardening_house = Int('gardening_house')
    s.add(And(1 <= gardening_house, gardening_house <= 4))
    for i in range(4):
        s.add(If(hobby[i] == gardening, gardening_house == i+1, True))

    s.add(white_house > gardening_house)

    # Clue 12: The person who loves a bouquet of daffodils is the person who loves yellow.
    for i in range(4):
        s.add(Implies(flower[i] == daffodils, color[i] == yellow))

    # Clue 13: The person living in a colonial-style house is the person whose favorite color is red.
    for i in range(4):
        s.add(Implies(house_style[i] == colonial, color[i] == red))

    # Clue 14: The person who has a cat is Eric.
    for i in range(4):
        s.add(Implies(pet[i] == cat, name[i] == Eric))

    # Check and get the model
    if s.check() == sat:
        m = s.model()
        
        # Function to get the string representation of a Z3 constant
        def get_value(z3_const, category_list):
            for val in category_list:
                if m.eval(z3_const).eq(m.eval(Const(val, z3_const.sort()))):
                    return val
            return None

        # Prepare the result rows
        rows = []
        for i in range(4):
            house_num = str(i+1)
            n_val = get_value(name[i], names)
            f_val = get_value(flower[i], flowers)
            h_val = get_value(hobby[i], hobbies)
            p_val = get_value(pet[i], pets)
            c_val = get_value(color[i], colors)
            hs_val = get_value(house_style[i], house_styles)
            rows.append([house_num, n_val, f_val, h_val, p_val, c_val, hs_val])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()