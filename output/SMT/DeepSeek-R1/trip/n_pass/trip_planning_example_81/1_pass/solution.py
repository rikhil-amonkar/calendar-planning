from z3 import *

def main():
    # City encoding
    M, B, H = 0, 1, 2
    cities = ["Mykonos", "Budapest", "Hamburg"]
    
    # Create solver
    s = Solver()
    
    # Variables for each day (0-indexed for days 1-9)
    start = [Int(f'start_{i+1}') for i in range(9)]
    flight = [Bool(f'flight_{i+1}') for i in range(9)]
    dest = [Int(f'dest_{i+1}') for i in range(9)]
    
    # Constraint: start and dest must be valid cities (0,1,2)
    for i in range(9):
        s.add(Or(start[i] == M, start[i] == B, start[i] == H))
        s.add(Or(dest[i] == M, dest[i] == B, dest[i] == H))
    
    # Flight constraints: if flight[i], then (start[i], dest[i]) must be a valid flight pair
    for i in range(9):
        s.add(Implies(flight[i], 
                      Or(
                         And(start[i] == M, dest[i] == B),
                         And(start[i] == B, dest[i] == M),
                         And(start[i] == B, dest[i] == H),
                         And(start[i] == H, dest[i] == B)
                      )))
        s.add(Implies(flight[i], start[i] != dest[i]))
    
    # Next day start constraint
    for i in range(8):  # from day1 to day8, set start of next day
        s.add(If(flight[i], start[i+1] == dest[i], start[i+1] == start[i]))
    
    # Presence of cities each day
    in_M = [Or(start[i] == M, And(flight[i], dest[i] == M)) for i in range(9)]
    in_B = [Or(start[i] == B, And(flight[i], dest[i] == B)) for i in range(9)]
    in_H = [Or(start[i] == H, And(flight[i], dest[i] == H)) for i in range(9)]
    
    # Total days per city
    s.add(Sum([If(in_M[i], 1, 0) for i in range(9)]) == 6)
    s.add(Sum([If(in_B[i], 1, 0) for i in range(9)]) == 3)
    s.add(Sum([If(in_H[i], 1, 0) for i in range(9)]) == 2)
    
    # Conference days: day4 (index3) and day9 (index8) must have Mykonos
    s.add(in_M[3] == True)  # day4
    s.add(in_M[8] == True)  # day9
    
    # Exactly 2 flight days
    s.add(Sum([If(flight[i], 1, 0) for i in range(9)]) == 2)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        start_val = [m.evaluate(start[i]).as_long() for i in range(9)]
        flight_val = [m.evaluate(flight[i]) for i in range(9)]
        dest_val = [m.evaluate(dest[i]).as_long() for i in range(9)]
        
        # Build itinerary records
        records = []
        current_block_start = 1
        current_city = start_val[0]
        
        for i in range(9):
            day = i + 1
            if flight_val[i]:
                if current_block_start <= day:
                    if current_block_start == day:
                        records.append({"day_range": f"Day {day}", "place": cities[current_city]})
                    else:
                        records.append({"day_range": f"Day {current_block_start}-{day}", "place": cities[current_city]})
                
                records.append({"day_range": f"Day {day}", "place": cities[current_city]})
                records.append({"day_range": f"Day {day}", "place": cities[dest_val[i]]})
                
                current_city = dest_val[i]
                current_block_start = day
            else:
                if day == 9:
                    if current_block_start == 9:
                        records.append({"day_range": f"Day {9}", "place": cities[current_city]})
                    else:
                        records.append({"day_range": f"Day {current_block_start}-{9}", "place": cities[current_city]})
        
        if not flight_val[8]:
            if current_block_start == 9:
                records.append({"day_range": f"Day {9}", "place": cities[current_city]})
            else:
                records.append({"day_range": f"Day {current_block_start}-{9}", "place": cities[current_city]})
        
        output = {"itinerary": records}
        print(output)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()