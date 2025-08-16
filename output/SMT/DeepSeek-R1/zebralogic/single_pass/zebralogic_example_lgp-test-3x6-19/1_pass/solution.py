from z3 import *

def main():
    # Define mappings from attribute values to integers
    name_dict = {'Arnold': 0, 'Eric': 1, 'Peter': 2}
    cigar_dict = {'pall mall': 0, 'blue master': 1, 'prince': 2}
    animal_dict = {'horse': 0, 'cat': 1, 'bird': 2}
    child_dict = {'Bella': 0, 'Fred': 1, 'Meredith': 2}
    book_dict = {'science fiction': 0, 'romance': 1, 'mystery': 2}
    phone_dict = {'google pixel 6': 0, 'iphone 13': 1, 'samsung galaxy s21': 2}
    
    # Reverse mappings for output
    rev_name = {v: k for k, v in name_dict.items()}
    rev_cigar = {v: k for k, v in cigar_dict.items()}
    rev_animal = {v: k for k, v in animal_dict.items()}
    rev_child = {v: k for k, v in child_dict.items()}
    rev_book = {v: k for k, v in book_dict.items()}
    rev_phone = {v: k for k, v in phone_dict.items()}
    
    # Create Z3 variables for each attribute in each house (houses 0,1,2 correspond to house1, house2, house3)
    names = [Int('name_%d' % i) for i in range(3)]
    cigars = [Int('cigar_%d' % i) for i in range(3)]
    animals = [Int('animal_%d' % i) for i in range(3)]
    children = [Int('child_%d' % i) for i in range(3)]
    book_genres = [Int('book_%d' % i) for i in range(3)]
    phone_models = [Int('phone_%d' % i) for i in range(3)]
    
    s = Solver()
    
    # Set domain for each variable: 0, 1, or 2
    for var_list in [names, cigars, animals, children, book_genres, phone_models]:
        for var in var_list:
            s.add(var >= 0, var < 3)
    
    # Uniqueness constraints
    s.add(Distinct(names))
    s.add(Distinct(cigars))
    s.add(Distinct(animals))
    s.add(Distinct(children))
    s.add(Distinct(book_genres))
    s.add(Distinct(phone_models))
    
    # Clue 1: Mystery book lover has child Fred
    for j in range(3):
        s.add(Implies(book_genres[j] == book_dict['mystery'], children[j] == child_dict['Fred']))
    
    # Clue 2: Cat owner is Eric
    for j in range(3):
        s.add(Implies(animals[j] == animal_dict['cat'], names[j] == name_dict['Eric']))
    
    # Clue 3: Pall Mall smoker in second house (index 1)
    s.add(cigars[1] == cigar_dict['pall mall'])
    
    # Clue 4: Horse owner has child Meredith
    for j in range(3):
        s.add(Implies(animals[j] == animal_dict['horse'], children[j] == child_dict['Meredith']))
    
    # Clue 5: Bella's parent smokes Prince
    for j in range(3):
        s.add(Implies(children[j] == child_dict['Bella'], cigars[j] == cigar_dict['prince']))
    
    # Clue 6: iPhone 13 directly left of Samsung Galaxy S21
    s.add(Or(
        And(phone_models[0] == phone_dict['iphone 13'], phone_models[1] == phone_dict['samsung galaxy s21']),
        And(phone_models[1] == phone_dict['iphone 13'], phone_models[2] == phone_dict['samsung galaxy s21'])
    ))
    
    # Clue 7: Fred's parent directly left of Arnold
    s.add(Or(
        And(children[0] == child_dict['Fred'], names[1] == name_dict['Arnold']),
        And(children[1] == child_dict['Fred'], names[2] == name_dict['Arnold'])
    ))
    
    # Clue 8: Peter left of Eric
    s.add(Or(
        And(names[0] == name_dict['Peter'], Or(names[1] == name_dict['Eric'], names[2] == name_dict['Eric'])),
        And(names[1] == name_dict['Peter'], names[2] == name_dict['Eric'])
    ))
    
    # Clue 9: Science fiction lover uses Samsung Galaxy S21
    for j in range(3):
        s.add(Implies(book_genres[j] == book_dict['science fiction'], phone_models[j] == phone_dict['samsung galaxy s21']))
    
    # Clue 10: Science fiction lover in third house (index 2)
    s.add(book_genres[2] == book_dict['science fiction'])
    
    # Clue 11: Mystery book lover not in second house (index 1)
    s.add(book_genres[1] != book_dict['mystery'])
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        rows = []
        for i in range(3):
            house = str(i+1)
            name_val = model.evaluate(names[i]).as_long()
            cigar_val = model.evaluate(cigars[i]).as_long()
            animal_val = model.evaluate(animals[i]).as_long()
            child_val = model.evaluate(children[i]).as_long()
            book_val = model.evaluate(book_genres[i]).as_long()
            phone_val = model.evaluate(phone_models[i]).as_long()
            
            row = [
                house,
                rev_name[name_val],
                rev_cigar[cigar_val],
                rev_animal[animal_val],
                rev_child[child_val],
                rev_book[book_val],
                rev_phone[phone_val]
            ]
            rows.append(row)
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                "rows": rows
            }
        }
        
        import json
        print(json.dumps(solution_dict, indent=4))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()