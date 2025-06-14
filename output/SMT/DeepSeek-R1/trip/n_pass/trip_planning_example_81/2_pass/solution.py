from z3 import *

def main():
    s = Solver()
    
    # Days are 1 to 9 (0-indexed: 0 to 8)
    start_city = [Int(f'start_{d}') for d in range(9)]
    end_city = [Int(f'end_{d}') for d in range(9)]
    
    # City mapping
    mykonos, budapest, hamburg = 0, 1, 2
    cities = [mykonos, budapest, hamburg]
    
    # Each city variable must be 0, 1, or 2
    for d in range(9):
        s.add(Or([start_city[d] == c for c in cities]))
        s.add(Or([end_city[d] == c for c in cities]))
    
    # Flight constraints: only direct flights between Budapest-Mykonos and Budapest-Hamburg
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
                 True))
    
    # Continuity: end of day d must match start of day d+1
    for d in range(8):
        s.add(end_city[d] == start_city[d+1])
    
    # Conference days: entire day in Mykonos (days 4 and 9)
    s.add(start_city[3] == mykonos, end_city[3] == mykonos)  # Day 4
    s.add(start_city[8] == mykonos, end_city[8] == mykonos)  # Day 9
    
    # Count days in each city (avoiding double-counting)
    myk_days = sum(If(start_city[d] == mykonos, 1, 0) for d in range(9))
    bud_days = sum(If(start_city[d] == budapest, 1, 0) for d in range(9))
    ham_days = sum(If(start_city[d] == hamburg, 1, 0) for d in range(9))
    
    myk_days += sum(If(And(end_city[d] == mykonos, start_city[d] != mykonos), 1, 0) for d in range(9))
    bud_days += sum(If(And(end_city[d] == budapest, start_city[d] != budapest), 1, 0) for d in range(9))
    ham_days += sum(If(And(end_city[d] == hamburg, start_city[d] != hamburg), 1, 0) for d in range(9))
    
    s.add(myk_days == 6, bud_days == 3, ham_days == 2)
    
    # Solve and print
    if s.check() == sat:
        m = s.model()
        names = {0: 'Mykonos', 1: 'Budapest', 2: 'Hamburg'}
        for d in range(9):
            start = m.eval(start_city[d]).as_long()
            end = m.eval(end_city[d]).as_long()
            if start == end:
                print(f"Day {d+1}: {names[start]}")
            else:
                print(f"Day {d+1}: {names[start]} and {names[end]}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()