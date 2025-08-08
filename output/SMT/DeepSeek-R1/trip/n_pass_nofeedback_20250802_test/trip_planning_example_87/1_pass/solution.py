from z3 import *

def main():
    # Cities: Riga=0, Amsterdam=1, Mykonos=2
    R, A, M = 0, 1, 2
    cities = ["Riga", "Amsterdam", "Mykonos"]
    
    # Create solver and variables
    s = Solver()
    c = [Int('c%d' % i) for i in range(8)]  # c0 to c7
    
    # Each city variable must be 0, 1, or 2
    for i in range(8):
        s.add(Or(c[i] == R, c[i] == A, c[i] == M))
    
    # Flight constraints: if we change city, it must be a direct flight
    for i in range(1, 8):
        prev = c[i-1]
        curr = c[i]
        flight_ok = Or(
            And(prev == R, curr == A),
            And(prev == A, curr == R),
            And(prev == A, curr == M),
            And(prev == M, curr == A)
        )
        s.add(If(prev == curr, True, flight_ok))
    
    # Total days for each city
    total_R = 0
    total_A = 0
    total_M = 0
    
    for i in range(1, 8):
        # Day i: uses c[i-1] and c[i]
        total_R += If(Or(c[i-1] == R, c[i] == R), 1, 0)
        total_A += If(Or(c[i-1] == A, c[i] == A), 1, 0)
        total_M += If(Or(c[i-1] == M, c[i] == M), 1, 0)
    
    s.add(total_R == 2, total_A == 2, total_M == 5)
    
    # Relative visit in Riga between day1 and day2: must be in Riga on day1 or day2
    day1_has_R = Or(c[0] == R, c[1] == R)
    day2_has_R = Or(c[1] == R, c[2] == R)
    s.add(Or(day1_has_R, day2_has_R))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Build the itinerary
        itinerary = []
        for day in range(1, 8):  # days 1 to 7
            idx_start = day - 1
            idx_end = day
            start_city_val = m.eval(c[idx_start])
            end_city_val = m.eval(c[idx_end])
            start_city_name = cities[int(str(start_city_val))]
            end_city_name = cities[int(str(end_city_val))]
            
            if start_city_val == end_city_val:
                itinerary.append({"day": day, "place": start_city_name})
            else:
                itinerary.append({"day": day, "place": start_city_name})
                itinerary.append({"day": day, "place": end_city_name})
        
        # Output as JSON dictionary
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()