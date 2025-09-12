import json
from z3 import *

def main():
    # Define the enums for names and vacations
    NameSort, (Bob, Peter, Alice, Eric, Carol, Arnold) = EnumSort('Name', ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold'])
    VacationSort, (mountain, camping, cruise, city, cultural, beach) = EnumSort('Vacation', ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach'])
    
    # Create arrays for names and vacations for each house (index 0 to 5 for houses 1 to 6)
    names = [Const(f'name_{i}', NameSort) for i in range(6)]
    vacations = [Const(f'vacation_{i}', VacationSort) for i in range(6)]
    
    s = Solver()
    
    # Each attribute is unique
    s.add(Distinct(names))
    s.add(Distinct(vacations))
    
    # Clue 3: Eric is in the second house
    s.add(names[1] == Eric)
    
    # Clue 4: Cultural vacation in third house
    s.add(vacations[2] == cultural)
    
    # Clue 7: Cultural vacation is Peter
    s.add(names[2] == Peter)
    
    # Clue 9: City vacation in fourth house
    s.add(vacations[3] == city)
    
    # Clue 2: Eric is right of Alice
    s.add(Or([And(names[i] == Alice, i < 1) for i in range(6)]))
    
    # Clue 1: Cultural left of beach
    s.add(Or([vacations[i] == beach for i in range(3, 6)]))
    
    # Clue 5: Bob directly left of Arnold
    s.add(Or([And(names[i] == Bob, names[i+1] == Arnold) for i in range(5)]))
    
    # Clue 6: Camping not in first house
    s.add(vacations[0] != camping)
    
    # Clue 8: Cruise vacation is Bob
    s.add(Or([And(names[i] == Bob, vacations[i] == cruise) for i in range(6)]))
    
    # Check satisfiability
    if s.check() == sat:
        model = s.model()
        name_list = ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold']
        vacation_list = ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach']
        
        rows = []
        for i in range(6):
            name_val = model.eval(names[i])
            vacation_val = model.eval(vacations[i])
            name_str = name_list[name_val.as_long()]
            vacation_str = vacation_list[vacation_val.as_long()]
            rows.append([str(i+1), name_str, vacation_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()