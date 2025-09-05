import json
from z3 import *

def main():
    # Create the solver
    solver = Solver()

    # Define the enums for each attribute
    NameSort, (arnold, peter, eric, alice) = EnumSort('Name', ['Arnold', 'Peter', 'Eric', 'Alice'])
    StyleSort, (craftsman, colonial, victorian, ranch) = EnumSort('Style', ['craftsman', 'colonial', 'victorian', 'ranch'])
    HairSort, (red, blonde, black, brown) = EnumSort('Hair', ['red', 'blonde', 'black', 'brown'])
    ChildSort, (bella, fred, meredith, samantha) = EnumSort('Child', ['Bella', 'Fred', 'Meredith', 'Samantha'])
    BookSort, (mystery, fantasy, romance, science_fiction) = EnumSort('Book', ['mystery', 'fantasy', 'romance', 'science fiction'])

    # Create arrays for each attribute for houses 1-4 (indexed 0-3)
    names = [Const(f'name_{i}', NameSort) for i in range(4)]
    styles = [Const(f'style_{i}', StyleSort) for i in range(4)]
    hairs = [Const(f'hair_{i}', HairSort) for i in range(4)]
    children = [Const(f'child_{i}', ChildSort) for i in range(4)]
    books = [Const(f'book_{i}', BookSort) for i in range(4)]

    # Add constraints that all attributes are distinct
    solver.add(Distinct(names))
    solver.add(Distinct(styles))
    solver.add(Distinct(hairs))
    solver.add(Distinct(children))
    solver.add(Distinct(books))

    # Clue 1: Craftsman house is third (index 2)
    solver.add(styles[2] == craftsman)

    # Clue 2: Alice loves romance books
    for i in range(4):
        solver.add(Implies(names[i] == alice, books[i] == romance))

    # Clue 3: Brown hair in fourth house (index 3)
    solver.add(hairs[3] == brown)

    # Clue 4: Child Samantha in fourth house (index 3)
    solver.add(children[3] == samantha)

    # Clue 5: Ranch house right of red hair
    red_hair_index = Int('red_hair_index')
    ranch_style_index = Int('ranch_style_index')
    solver.add(red_hair_index >= 0, red_hair_index < 4)
    solver.add(ranch_style_index >= 0, ranch_style_index < 4)
    for i in range(4):
        solver.add(Implies(hairs[i] == red, red_hair_index == i))
        solver.add(Implies(styles[i] == ranch, ranch_style_index == i))
    solver.add(ranch_style_index > red_hair_index)

    # Clue 6: Peter has child Bella
    for i in range(4):
        solver.add(Implies(names[i] == peter, children[i] == bella))

    # Clue 7: Arnold has red hair
    for i in range(4):
        solver.add(Implies(names[i] == arnold, hairs[i] == red))

    # Clue 8: Alice in colonial house
    for i in range(4):
        solver.add(Implies(names[i] == alice, styles[i] == colonial))

    # Clue 9: Black hair in second house (index 1)
    solver.add(hairs[1] == black)

    # Clue 10: Peter loves fantasy books
    for i in range(4):
        solver.add(Implies(books[i] == fantasy, names[i] == peter))

    # Clue 11: Arnold has child Meredith
    for i in range(4):
        solver.add(Implies(names[i] == arnold, children[i] == meredith))

    # Clue 12: Black hair is Eric
    for i in range(4):
        solver.add(Implies(hairs[i] == black, names[i] == eric))

    # Clue 13: Arnold loves science fiction books
    for i in range(4):
        solver.add(Implies(books[i] == science_fiction, names[i] == arnold))

    # Check if satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Map house indices to attribute values
        result = []
        attr_names = ["Name", "HouseStyle", "HairColor", "Children", "BookGenre"]
        for i in range(4):
            name_val = model.eval(names[i])
            style_val = model.eval(styles[i])
            hair_val = model.eval(hairs[i])
            child_val = model.eval(children[i])
            book_val = model.eval(books[i])
            
            # Convert Z3 symbols to strings
            row = [
                str(i+1),
                str(name_val),
                str(style_val),
                str(hair_val),
                str(child_val),
                str(book_val)
            ]
            result.append(row)
        
        # Format the JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()