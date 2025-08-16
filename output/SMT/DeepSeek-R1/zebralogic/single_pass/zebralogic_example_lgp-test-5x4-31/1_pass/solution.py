from z3 import *
import json

def main():
    # Define the sorts and constants for each attribute
    NameSort, name_consts = EnumSort('Name', ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter'])
    VacationSort, vacation_consts = EnumSort('Vacation', ['cruise', 'city', 'camping', 'beach', 'mountain'])
    ChildrenSort, children_consts = EnumSort('Children', ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy'])
    NationalitySort, nationality_consts = EnumSort('Nationality', ['dane', 'norwegian', 'brit', 'german', 'swede'])
    
    Alice, Bob, Arnold, Eric, Peter = name_consts
    cruise, city, camping, beach, mountain = vacation_consts
    Bella, Samantha, Fred, Meredith, Timothy = children_consts
    dane, norwegian, brit, german, swede = nationality_consts
    
    # Create variables for each house
    n = [Const(f'n_{i}', NameSort) for i in range(5)]  # names
    v = [Const(f'v_{i}', VacationSort) for i in range(5)]  # vacations
    c = [Const(f'c_{i}', ChildrenSort) for i in range(5)]  # children
    nat = [Const(f'nat_{i}', NationalitySort) for i in range(5)]  # nationalities
    
    solver = Solver()
    
    # All attributes must be unique
    solver.add(Distinct(n))
    solver.add(Distinct(v))
    solver.add(Distinct(c))
    solver.add(Distinct(nat))
    
    # Clue 1: The Norwegian is Peter.
    for i in range(5):
        solver.add((nat[i] == norwegian) == (n[i] == Peter))
    
    # Clue 2: The Swedish person is the person whose child is named Bella.
    for i in range(5):
        solver.add((nat[i] == swede) == (c[i] == Bella))
    
    # Clue 3: The person who loves beach vacations is directly left of the person whose child is named Samantha.
    for i in range(4):  # houses 1 to 4 (0-indexed: 0,1,2,3)
        solver.add(Implies(v[i] == beach, c[i+1] == Samantha))
    # Also, ensure there is at least one beach with Samantha to the immediate right
    solver.add(Or([And(v[i] == beach, c[i+1] == Samantha) for i in range(4)]))
    
    # Clue 4: The person whose child is named Bella is not in the second house (index1).
    solver.add(c[1] != Bella)
    
    # Clue 5: Alice is the British person.
    for i in range(5):
        solver.add((n[i] == Alice) == (nat[i] == brit))
    
    # Clue 6: The person who likes going on cruises is in the first house (index0).
    solver.add(v[0] == cruise)
    
    # Clue 7: The person whose child is named Meredith is in the fourth house (index3).
    solver.add(c[3] == Meredith)
    
    # Clue 8: Eric is not in the fifth house (index4).
    solver.add(n[4] != Eric)
    
    # Clue 9: The Swedish person is somewhere to the right of the Norwegian.
    # For each house i, if it's Norwegian, then Swede must be in a house j>i.
    for i in range(5):
        solver.add(Implies(nat[i] == norwegian, 
                          Or([nat[j] == swede for j in range(i+1, 5)])))
    
    # Clue 10: There is one house between the person whose child is named Fred and the person who prefers city breaks.
    # Two cases: Fred left of city by two, or city left of Fred by two.
    case1 = Or([And(c[i] == Fred, v[i+2] == city) for i in range(3)])  # i from 0 to 2
    case2 = Or([And(v[i] == city, c[i+2] == Fred) for i in range(3)])
    solver.add(Or(case1, case2))
    
    # Clue 11: Bob is the person who enjoys camping trips.
    for i in range(5):
        solver.add((n[i] == Bob) == (v[i] == camping))
    
    # Clue 12: The Dane is in the fifth house (index4).
    solver.add(nat[4] == dane)
    
    # Clue 13: The person who enjoys camping trips is not in the fifth house (index4).
    solver.add(v[4] != camping)
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        rows = []
        for i in range(5):
            name_val = model.evaluate(n[i])
            vacation_val = model.evaluate(v[i])
            child_val = model.evaluate(c[i])
            nationality_val = model.evaluate(nat[i])
            
            # Convert to string by comparing with the constants
            name_str = None
            for j, const in enumerate(name_consts):
                if eq(name_val, const):
                    name_str = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter'][j]
                    break
            
            vacation_str = None
            for j, const in enumerate(vacation_consts):
                if eq(vacation_val, const):
                    vacation_str = ['cruise', 'city', 'camping', 'beach', 'mountain'][j]
                    break
            
            child_str = None
            for j, const in enumerate(children_consts):
                if eq(child_val, const):
                    child_str = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy'][j]
                    break
            
            nationality_str = None
            for j, const in enumerate(nationality_consts):
                if eq(nationality_val, const):
                    nationality_str = ['dane', 'norwegian', 'brit', 'german', 'swede'][j]
                    break
            
            row = [str(i+1), name_str, vacation_str, child_str, nationality_str]
            rows.append(row)
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()