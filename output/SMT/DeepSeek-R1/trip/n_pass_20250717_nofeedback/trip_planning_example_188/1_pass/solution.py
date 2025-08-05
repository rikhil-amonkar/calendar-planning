from z3 import *
import json

def main():
    # Create the city mapping
    city_names = {
        0: "Brussels",
        1: "Barcelona",
        2: "Split"
    }
    
    # We have 12 days
    n_days = 12
    n_flights = n_days - 1  # flights from day1 to day11

    # L[i] is the starting city at the beginning of day i (0-indexed, so day0 is day1)
    L = [Int('L_%d' % i) for i in range(n_days)]
    # F[i] is whether we fly on day i+1 (connecting day i+1 and day i+2). For i from 0 to 10 (day1 to day11)
    F = [Bool('F_%d' % i) for i in range(n_flights)]
    
    s = Solver()
    
    # Constraint: L[0] must be Brussels (0)
    s.add(L[0] == 0)
    
    # Constraint: no flight on day1 (so that we start day2 in Brussels)
    s.add(F[0] == False)
    
    # Constraints for each flight day and the next day's city
    for i in range(n_flights):
        # If we fly on day i+1, then the next city must be reachable by a direct flight
        s.add(If(F[i],
                 Or(
                     And(L[i] == 0, L[i+1] == 1),   # Brussels <-> Barcelona
                     And(L[i] == 1, L[i+1] == 0),
                     And(L[i] == 1, L[i+1] == 2),   # Barcelona <-> Split
                     And(L[i] == 2, L[i+1] == 1)
                 ),
                 L[i+1] == L[i]   # if not flying, same city next day
                ))
    
    # Constraints for the domain of L: only 0,1,2
    for i in range(n_days):
        s.add(Or(L[i] == 0, L[i] == 1, L[i] == 2))
    
    # Now, define the total days per city
    days_B = 0
    days_A = 0
    days_S = 0
    
    # For each day j (0-indexed, representing day j+1)
    for j in range(n_days):
        if j < n_flights:  # j from 0 to 10 (days 1 to 11)
            # On day j+1, we are in L[j] and if we fly (F[j]) then also in L[j+1]
            in_B = Or(L[j] == 0, And(F[j], L[j+1] == 0))
            in_A = Or(L[j] == 1, And(F[j], L[j+1] == 1))
            in_S = Or(L[j] == 2, And(F[j], L[j+1] == 2))
        else:  # j = 11 (day12)
            in_B = (L[j] == 0)
            in_A = (L[j] == 1)
            in_S = (L[j] == 2)
        
        days_B += If(in_B, 1, 0)
        days_A += If(in_A, 1, 0)
        days_S += If(in_S, 1, 0)
    
    s.add(days_B == 2)
    s.add(days_A == 7)
    s.add(days_S == 5)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract the values for L and F
        L_val = [m.evaluate(L[i]).as_long() for i in range(n_days)]
        F_val = [is_true(m.evaluate(F[i])) for i in range(n_flights)]
        
        # Build the itinerary
        itinerary_list = []
        for j in range(n_days):
            day = j + 1
            if j < n_flights and F_val[j]:
                # Flight on day j+1: we are in both L[j] and L[j+1]
                cities_set = { L_val[j], L_val[j+1] }
            else:
                cities_set = { L_val[j] }
            
            # Convert to city names and sort alphabetically
            cities_names = sorted([city_names[code] for code in cities_set])
            itinerary_list.append({"day": day, "cities": cities_names})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()