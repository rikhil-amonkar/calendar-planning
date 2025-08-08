from z3 import *
import json

def main():
    # Cities mapping
    cities = {0: "Bucharest", 1: "Lyon", 2: "Porto"}
    n_days = 16
    
    # Morning and evening city variables for each day
    M = [Int('M_%d' % (i+1)) for i in range(n_days)]
    E = [Int('E_%d' % (i+1)) for i in range(n_days)]
    
    s = Solver()
    
    # Constraint: Each M_i and E_i must be 0, 1, or 2
    for i in range(n_days):
        s.add(And(M[i] >= 0, M[i] <= 2))
        s.add(And(E[i] >= 0, E[i] <= 2))
    
    # Continuity constraint: E_i must equal M_{i+1} for i in [0, n_days-2]
    for i in range(n_days - 1):
        s.add(E[i] == M[i+1])
    
    # Valid direct flights: (Bucharest, Lyon), (Lyon, Bucharest), (Lyon, Porto), (Porto, Lyon)
    valid_flights = [(0, 1), (1, 0), (1, 2), (2, 1)]
    
    # Flight constraint: if M_i != E_i, then (M_i, E_i) must be a valid flight
    for i in range(n_days):
        flight_cond = Or([And(M[i] == a, E[i] == b) for (a, b) in valid_flights])
        s.add(If(M[i] != E[i], flight_cond, True))
    
    # Total days in each city
    b_days = 0
    l_days = 0
    p_days = 0
    
    for i in range(n_days):
        # Count morning city
        b_days += If(M[i] == 0, 1, 0)
        l_days += If(M[i] == 1, 1, 0)
        p_days += If(M[i] == 2, 1, 0)
        
        # Count evening city if it's a flight day (M_i != E_i)
        b_days += If(And(E[i] == 0, M[i] != 0), 1, 0)
        l_days += If(And(E[i] == 1, M[i] != 1), 1, 0)
        p_days += If(And(E[i] == 2, M[i] != 2), 1, 0)
    
    s.add(b_days == 7)
    s.add(l_days == 7)
    s.add(p_days == 4)
    
    # Wedding constraint: must be in Bucharest on at least one day between 1 and 7
    wedding_days = []
    for i in range(7):  # Days 1 to 7 (indices 0 to 6)
        wedding_days.append(Or(M[i] == 0, E[i] == 0))
    s.add(Or(wedding_days))
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        M_vals = [model.evaluate(M[i]).as_long() for i in range(n_days)]
        E_vals = [model.evaluate(E[i]).as_long() for i in range(n_days)]
        
        # Build the itinerary per day
        daily_places = []
        for i in range(n_days):
            if M_vals[i] == E_vals[i]:
                place_str = cities[M_vals[i]]
            else:
                place_str = cities[M_vals[i]] + " and " + cities[E_vals[i]]
            daily_places.append(place_str)
        
        # Aggregate consecutive days with the same place string
        segments = []
        start_day = 1
        current_place = daily_places[0]
        
        for day in range(1, n_days):
            if daily_places[day] == current_place and " and " not in current_place:
                continue
            else:
                end_day = day
                if start_day == end_day:
                    day_range_str = "Day " + str(start_day)
                else:
                    day_range_str = "Day " + str(start_day) + "-" + str(end_day)
                segments.append({"day_range": day_range_str, "place": current_place})
                start_day = day + 1
                current_place = daily_places[day]
        
        # Add the last segment
        if start_day == n_days:
            day_range_str = "Day " + str(n_days)
        else:
            day_range_str = "Day " + str(start_day) + "-" + str(n_days)
        segments.append({"day_range": day_range_str, "place": current_place})
        
        # Output the itinerary as JSON
        result = {"itinerary": segments}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()