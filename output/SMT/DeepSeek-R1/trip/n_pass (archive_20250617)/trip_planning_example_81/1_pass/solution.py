from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Days are 1 to 9, we use 0-indexed arrays for start_city and end_city
    start_city = [Int(f'start_city_{d+1}') for d in range(9)]
    end_city = [Int(f'end_city_{d+1}') for d in range(9)]
    
    # City mapping: 0 = Mykonos, 1 = Budapest, 2 = Hamburg
    mykonos = 0
    budapest = 1
    hamburg = 2
    
    # Each city variable must be 0, 1, or 2
    for d in range(9):
        s.add(Or(start_city[d] == mykonos, start_city[d] == budapest, start_city[d] == hamburg))
        s.add(Or(end_city[d] == mykonos, end_city[d] == budapest, end_city[d] == hamburg))
    
    # Flight constraints: direct flights between Budapest-Mykonos and Budapest-Hamburg
    for d in range(9):
        start = start_city[d]
        end = end_city[d]
        s.add(If(start != end,
                 Or(
                    And(start == budapest, end == mykonos),
                    And(start == mykonos, end == budapest),
                    And(start == budapest, end == hamburg),
                    And(start == hamburg, end == budapest)
                 ),
                 True))  # If same city, no flight needed
    
    # Continuity: end_city of day d must be start_city of day d+1 for d in 0 to 7 (days 1 to 8)
    for d in range(8):
        s.add(end_city[d] == start_city[d+1])
    
    # Conference constraints: must be in Mykonos on day 4 (index 3) and day 9 (index 8)
    s.add(Or(start_city[3] == mykonos, end_city[3] == mykonos))  # Day 4
    s.add(Or(start_city[8] == mykonos, end_city[8] == mykonos))  # Day 9
    
    # Count days in each city
    myk_days = 0
    bud_days = 0
    ham_days = 0
    
    for d in range(9):
        # For Mykonos
        myk_days += If(start_city[d] == mykonos, 1, 0)
        myk_days += If(And(end_city[d] == mykonos, start_city[d] != mykonos), 1, 0)
        
        # For Budapest
        bud_days += If(start_city[d] == budapest, 1, 0)
        bud_days += If(And(end_city[d] == budapest, start_city[d] != budapest), 1, 0)
        
        # For Hamburg
        ham_days += If(start_city[d] == hamburg, 1, 0)
        ham_days += If(And(end_city[d] == hamburg, start_city[d] != hamburg), 1, 0)
    
    # Add total day constraints
    s.add(myk_days == 6)
    s.add(bud_days == 3)
    s.add(ham_days == 2)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        city_names = {0: 'Mykonos', 1: 'Budapest', 2: 'Hamburg'}
        for d in range(9):
            start_val = m.eval(start_city[d]).as_long()
            end_val = m.eval(end_city[d]).as_long()
            if start_val == end_val:
                print(f"Day {d+1}: {city_names[start_val]}")
            else:
                print(f"Day {d+1}: {city_names[start_val]} and {city_names[end_val]}")
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()