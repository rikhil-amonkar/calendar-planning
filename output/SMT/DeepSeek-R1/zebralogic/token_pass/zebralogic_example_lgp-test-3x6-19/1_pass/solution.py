import json
from z3 import *

def main():
    # Initialize solver
    s = Solver()

    # Define attributes as enums
    Name = Datatype('Name')
    Name.declare('Arnold')
    Name.declare('Eric')
    Name.declare('Peter')
    Name = Name.create()

    Cigar = Datatype('Cigar')
    Cigar.declare('pall_mall')
    Cigar.declare('blue_master')
    Cigar.declare('prince')
    Cigar = Cigar.create()

    Animal = Datatype('Animal')
    Animal.declare('horse')
    Animal.declare('cat')
    Animal.declare('bird')
    Animal = Animal.create()

    Children = Datatype('Children')
    Children.declare('Bella')
    Children.declare('Fred')
    Children.declare('Meredith')
    Children = Children.create()

    BookGenre = Datatype('BookGenre')
    BookGenre.declare('science_fiction')
    BookGenre.declare('romance')
    BookGenre.declare('mystery')
    BookGenre = BookGenre.create()

    PhoneModel = Datatype('PhoneModel')
    PhoneModel.declare('google_pixel_6')
    PhoneModel.declare('iphone_13')
    PhoneModel.declare('samsung_galaxy_s21')
    PhoneModel = PhoneModel.create()

    # Create variables for each house attribute
    houses = [1, 2, 3]
    name = [Const(f'name_{i}', Name) for i in houses]
    cigar = [Const(f'cigar_{i}', Cigar) for i in houses]
    animal = [Const(f'animal_{i}', Animal) for i in houses]
    children = [Const(f'children_{i}', Children) for i in houses]
    book_genre = [Const(f'book_genre_{i}', BookGenre) for i in houses]
    phone_model = [Const(f'phone_model_{i}', PhoneModel) for i in houses]

    # Add uniqueness constraints
    s.add(Distinct(name))
    s.add(Distinct(cigar))
    s.add(Distinct(animal))
    s.add(Distinct(children))
    s.add(Distinct(book_genre))
    s.add(Distinct(phone_model))

    # Clue 1: The person who loves mystery books is the person's child is named Fred.
    s.add(ForAll([x], Implies(book_genre[x] == BookGenre.mystery, children[x] == Children.Fred)))

    # Clue 2: The cat lover is Eric.
    s.add(ForAll([x], Implies(animal[x] == Animal.cat, name[x] == Name.Eric)))

    # Clue 3: The person partial to Pall Mall is in the second house.
    s.add(cigar[1] == Cigar.pall_mall)

    # Clue 4: The person who keeps horses is the person's child is named Meredith.
    s.add(ForAll([x], Implies(animal[x] == Animal.horse, children[x] == Children.Meredith)))

    # Clue 5: The person's child is named Bella is the Prince smoker.
    s.add(ForAll([x], Implies(children[x] == Children.Bella, cigar[x] == Cigar.prince)))

    # Clue 6: The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
    s.add(phone_model[0] == PhoneModel.iphone_13, phone_model[1] == PhoneModel.samsung_galaxy_s21)

    # Clue 7: The person's child is named Fred is directly left of Arnold.
    s.add(Exists([x], And(children[x] == Children.Fred, name[x+1] == Name.Arnold)))

    # Clue 8: Peter is somewhere to the left of Eric.
    pete_pos = Const('pete_pos', IntSort())
    eric_pos = Const('eric_pos', IntSort())
    s.add(Exists([x, y], And(name[x] == Name.Peter, name[y] == Name.Eric, x < y)))

    # Clue 9: The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
    s.add(ForAll([x], Implies(book_genre[x] == BookGenre.science_fiction, phone_model[x] == PhoneModel.samsung_galaxy_s21)))

    # Clue 10: The person who loves science fiction books is in the third house.
    s.add(book_genre[2] == BookGenre.science_fiction)

    # Clue 11: The person who loves mystery books is not in the second house.
    s.add(book_genre[1] != BookGenre.mystery)

    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        
        # Prepare results
        rows = []
        for i in houses:
            idx = i-1
            n = m.eval(name[idx])
            c = m.eval(cigar[idx])
            a = m.eval(animal[idx])
            ch = m.eval(children[idx])
            bg = m.eval(book_genre[idx])
            pm = m.eval(phone_model[idx])
            
            # Convert to string representation
            row = [
                str(i),
                str(n).replace('_', ' '),
                str(c).replace('_', ' '),
                str(a).replace('_', ' '),
                str(ch).replace('_', ' '),
                str(bg).replace('_', ' '),
                str(pm).replace('_', ' ')
            ]
            rows.append(row)
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()