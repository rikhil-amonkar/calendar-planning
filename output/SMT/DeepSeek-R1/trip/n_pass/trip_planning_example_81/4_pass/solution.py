from z3 import *

def main():
    s = Solver()
    
    # Days are 1 to 9 (0-indexed: 0 to 8)
    start_city = [Int(f'start_{d}') for d in range(9)]
    end_city = [Int(f'end_{d}') for d in range(9)]
    
    # City mapping: 0=Mykonos, 1=Budapest, 2=Hamburg
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
    
    # Continuity: end of day d must be start of day d+1
    for d in range(8):
        s.add(end_city[d] == start_city[d+1])
    
    # Conference days: must start in Mykonos
    s.add(start_city[3] == mykonos)  # Day 4
    s.add(start_city[8] == mykonos)  # Day 9
    
    # End day 9 in Budapest to satisfy international airport requirement
    s.add(end_city[8] == budapest)
    
    # Start in international airport (Budapest or Hamburg)
    s.add(Or(start_city[0] == budapest, start_city[0] == hamburg))
    
    # Count days in each city
    myk_days = Sum([If(Or(start_city[d] == mykonos, end_city[d] == mykonos), 1, 0) for d in range(9)])
    bud_days = Sum([If(Or(start_city[d] == budapest, end_city[d] == budapest), 1, 0) for d in range(9)])
    ham_days = Sum([If(Or(start_city[d] == hamburg, end_city[d] == hamburg), 1, 0) for d in range(9)])
    
    s.add(myk_days == 6, bud_days == 3, ham_days == 2)
    
    # Solve and print
    if s.check() == sat:
        m = s.model()
        names = {0: 'Mykonos', 1: 'Budapest', 2: 'Hamburg'}
        for d in range(9):
            start_val = m.eval(start_city[d]).as_long()
            end_val = m.eval(end_city[d]).as_long()
            if start_val == end_val:
                print(f"Day {d+1}: {names[start_val]}")
            else:
                print(f"Day {d+1}: {names[start_val]} and {names[end_val]}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()