from z3 import *

def main():
    # Define the string lists for attributes
    name_strings = ['Eric', 'Peter', 'Alice', 'Arnold']
    car_strings = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
    bd_strings = ['jan', 'april', 'sept', 'feb']
    hobby_strings = ['painting', 'cooking', 'gardening', 'photography']

    # Create EnumSorts
    NameSort, name_consts = EnumSort('Name', name_strings)
    CarSort, car_consts = EnumSort('Car', car_strings)
    BirthdaySort, bd_consts = EnumSort('Birthday', bd_strings)
    HobbySort, hobby_consts = EnumSort('Hobby', hobby_strings)
    
    # Unpack constants
    Eric, Peter, Alice, Arnold = name_consts
    tesla_model_3, honda_civic, toyota_camry, ford_f150 = car_consts
    jan, april, sept, feb = bd_consts
    painting, cooking, gardening, photography = hobby_consts

    # Variables for each house (0-indexed: house1=0, house2=1, etc.)
    n = [Const('n_%d' % i, NameSort) for i in range(4)]
    c = [Const('c_%d' % i, CarSort) for i in range(4)]
    b = [Const('b_%d' % i, BirthdaySort) for i in range(4)]
    h = [Const('h_%d' % i, HobbySort) for i in range(4)]
    
    s = Solver()
    
    # All attributes must be distinct
    s.add(Distinct(n))
    s.add(Distinct(c))
    s.add(Distinct(b))
    s.add(Distinct(h))
    
    # Clue 1: January birthday not in second house (index1)
    s.add(b[1] != jan)
    
    # Helper function to get house index (0-based) of a value in a list of variables
    def get_index(vars, val):
        return If(vars[0] == val, 0,
               If(vars[1] == val, 1,
               If(vars[2] == val, 2, 3)))
    
    # Clue 2: Photography left of Eric
    eric_house = get_index(n, Eric)
    photo_house = get_index(h, photography)
    s.add(photo_house < eric_house)
    
    # Clue 3: Photography left of Peter
    peter_house = get_index(n, Peter)
    s.add(photo_house < peter_house)
    
    # Clue 4: Honda Civic directly left of Tesla Model 3
    honda_house = get_index(c, honda_civic)
    tesla_house = get_index(c, tesla_model_3)
    s.add(honda_house == tesla_house - 1)
    
    # Clue 5: One house between Tesla Model 3 and gardening
    gardening_house = get_index(h, gardening)
    s.add(Or(tesla_house == gardening_house - 2, tesla_house == gardening_house + 2))
    
    # Clue 6: Tesla Model 3 owner is Arnold
    for i in range(4):
        s.add(Implies(c[i] == tesla_model_3, n[i] == Arnold))
    
    # Clue 7: February birthday is cooking hobby
    for i in range(4):
        s.add((b[i] == feb) == (h[i] == cooking))
    
    # Clue 8: Toyota Camry owner is Peter
    for i in range(4):
        s.add(Implies(c[i] == toyota_camry, n[i] == Peter))
    
    # Clue 9: April birthday is Arnold
    for i in range(4):
        s.add(Implies(b[i] == april, n[i] == Arnold))
    
    # Clue 10: Alice is photography enthusiast
    for i in range(4):
        s.add((n[i] == Alice) == (h[i] == photography))
    
    # Clue 11: Peter is January birthday
    for i in range(4):
        s.add((n[i] == Peter) == (b[i] == jan))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(4):
            # Get the actual values from the model
            n_val = m[n[i]]
            c_val = m[c[i]]
            b_val = m[b[i]]
            h_val = m[h[i]]
            
            # Convert to string by comparing with the constants
            name_str = None
            for j in range(4):
                if n_val.eq(name_consts[j]):
                    name_str = name_strings[j]
                    break
            car_str = None
            for j in range(4):
                if c_val.eq(car_consts[j]):
                    car_str = car_strings[j]
                    break
            bd_str = None
            for j in range(4):
                if b_val.eq(bd_consts[j]):
                    bd_str = bd_strings[j]
                    break
            hobby_str = None
            for j in range(4):
                if h_val.eq(hobby_consts[j]):
                    hobby_str = hobby_strings[j]
                    break
            
            # Create the row for house i+1
            house_num = str(i+1)
            row = [house_num, name_str, car_str, bd_str, hobby_str]
            rows.append(row)
        
        # Build the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                "rows": rows
            }
        }
        # Output as JSON string
        print(solution_dict)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()