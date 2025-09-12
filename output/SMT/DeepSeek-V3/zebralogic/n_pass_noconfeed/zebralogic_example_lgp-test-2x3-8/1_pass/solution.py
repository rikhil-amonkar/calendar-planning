import z3
import json

def main():
    solver = z3.Solver()
    
    # Define attributes and their possible values
    names = ['Arnold', 'Eric']
    birthdays = ['april', 'sept']
    mothers = ['Aniya', 'Holly']
    
    # Create variables for each house attribute
    house_name = [z3.Int(f'name_{i}') for i in range(1, 3)]
    house_birthday = [z3.Int(f'birthday_{i}') for i in range(1, 3)]
    house_mother = [z3.Int(f'mother_{i}') for i in range(1, 3)]
    
    # Define domains for each variable
    for i in range(2):
        solver.add(z3.And(house_name[i] >= 0, house_name[i] < 2))
        solver.add(z3.And(house_birthday[i] >= 0, house_birthday[i] < 2))
        solver.add(z3.And(house_mother[i] >= 0, house_mother[i] < 2))
    
    # All attributes within each category must be unique
    solver.add(z3.Distinct(house_name))
    solver.add(z3.Distinct(house_birthday))
    solver.add(z3.Distinct(house_mother))
    
    # Clue 1: Eric is somewhere to the left of The person whose mother's name is Holly
    # Eric has index 1 in names list (0=Arnold, 1=Eric)
    # Holly has index 1 in mothers list (0=Aniya, 1=Holly)
    eric_position = z3.Int('eric_pos')
    holly_mother_position = z3.Int('holly_mother_pos')
    
    solver.add(eric_position >= 0)
    solver.add(eric_position < 2)
    solver.add(holly_mother_position >= 0)
    solver.add(holly_mother_position < 2)
    
    # Find positions of Eric and Holly's mother child
    for i in range(2):
        solver.add(z3.Implies(house_name[i] == 1, eric_position == i))
        solver.add(z3.Implies(house_mother[i] == 1, holly_mother_position == i))
    
    solver.add(eric_position < holly_mother_position)
    
    # Clue 2: The person whose birthday is in April is in the first house
    # April has index 0 in birthdays list (0=april, 1=sept)
    solver.add(house_birthday[0] == 0)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare result data
        result = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother"],
                "rows": []
            }
        }
        
        for i in range(2):
            name_idx = model.eval(house_name[i]).as_long()
            birthday_idx = model.eval(house_birthday[i]).as_long()
            mother_idx = model.eval(house_mother[i]).as_long()
            
            row = [
                str(i + 1),
                names[name_idx],
                birthdays[birthday_idx],
                mothers[mother_idx]
            ]
            result["solution"]["rows"].append(row)
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()