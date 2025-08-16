from z3 import *

def main():
    # Define enums for attributes
    Name = Datatype('Name')
    Name.declare('Arnold')
    Name.declare('Peter')
    Name.declare('Carol')
    Name.declare('Alice')
    Name.declare('Bob')
    Name.declare('Eric')
    Name = Name.create()

    Child = Datatype('Child')
    Child.declare('Alice')
    Child.declare('Timothy')
    Child.declare('Bella')
    Child.declare('Meredith')
    Child.declare('Fred')
    Child.declare('Samantha')
    Child = Child.create()

    Smoothie = Datatype('Smoothie')
    Smoothie.declare('desert')
    Smoothie.declare('cherry')
    Smoothie.declare('watermelon')
    Smoothie.declare('blueberry')
    Smoothie.declare('lime')
    Smoothie.declare('dragonfruit')
    Smoothie = Smoothie.create()

    # Create variables for each house (0-indexed: house0 = house1, house5 = house6)
    names = [Const(f'name_{i}', Name) for i in range(6)]
    children = [Const(f'child_{i}', Child) for i in range(6)]
    smoothies = [Const(f'smoothie_{i}', Smoothie) for i in range(6)]

    s = Solver()

    # All attributes must be unique
    s.add(Distinct(names))
    s.add(Distinct(children))
    s.add(Distinct(smoothies))

    # Clue 13 and 14: House 6 has child Meredith and smoothie dragonfruit
    s.add(children[5] == Child.Meredith)
    s.add(smoothies[5] == Smoothie.dragonfruit)

    # Clue 6 and 7: Alice (person) has child Alice and smoothie watermelon
    for i in range(6):
        s.add(Implies(names[i] == Name.Alice, children[i] == Child.Alice))
        s.add(Implies(names[i] == Name.Alice, smoothies[i] == Smoothie.watermelon))

    # Clue 3: Alice not in house 5 (index 4)
    s.add(names[4] != Name.Alice)

    # Clue 4: Child Samantha not in house 2 (index 1)
    s.add(children[1] != Child.Samantha)

    # Clue 9: Arnold not in house 2 (index 1)
    s.add(names[1] != Name.Arnold)

    # Clue 10: Bob has child Timothy
    for i in range(6):
        s.add(Implies(names[i] == Name.Bob, children[i] == Child.Timothy))

    # Clue 11: Arnold directly left of Carol
    s.add(Or([And(names[i] == Name.Arnold, names[i+1] == Name.Carol) for i in range(5)]))

    # Clue 12: Cherry smoothie directly left of child Samantha
    s.add(Or([And(smoothies[i] == Smoothie.cherry, children[i+1] == Child.Samantha) for i in range(5)]))

    # Clue 1: Child Fred and desert smoothie are adjacent
    adj_constraints = []
    for i in range(5):
        adj_constraints.append(And(children[i] == Child.Fred, smoothies[i+1] == Smoothie.desert))
        adj_constraints.append(And(children[i+1] == Child.Fred, smoothies[i] == Smoothie.desert))
    s.add(Or(adj_constraints))

    # Clue 2: Blueberry smoothie left of child Fred (using positions)
    blueberry_house = Int('blueberry_house')
    s.add(blueberry_house >= 1, blueberry_house <= 6)
    for i in range(6):
        s.add((smoothies[i] == Smoothie.blueberry) == (blueberry_house == i+1))
    
    fred_child_house = Int('fred_child_house')
    s.add(fred_child_house >= 1, fred_child_house <= 6)
    for i in range(6):
        s.add((children[i] == Child.Fred) == (fred_child_house == i+1))
    
    s.add(blueberry_house < fred_child_house)

    # Clue 5: Watermelon smoothie right of cherry smoothie
    watermelon_right_of_cherry = []
    for i in range(5):
        for j in range(i+1, 6):
            watermelon_right_of_cherry.append(And(smoothies[i] == Smoothie.cherry, smoothies[j] == Smoothie.watermelon))
    s.add(Or(watermelon_right_of_cherry))

    # Clue 8: Peter right of child Samantha
    peter_right_of_samantha = []
    for i in range(5):
        for j in range(i+1, 6):
            peter_right_of_samantha.append(And(children[i] == Child.Samantha, names[j] == Name.Peter))
    s.add(Or(peter_right_of_samantha))

    # Solve the model
    if s.check() == sat:
        m = s.model()
        result = []
        for i in range(6):
            name_val = m[names[i]]
            child_val = m[children[i]]
            smoothie_val = m[smoothies[i]]
            name_str = name_val.decl().name()
            child_str = child_val.decl().name()
            smoothie_str = smoothie_val.decl().name()
            result.append([str(i+1), name_str, child_str, smoothie_str])
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Children", "Smoothie"],
                "rows": result
            }
        }
        print(output)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()