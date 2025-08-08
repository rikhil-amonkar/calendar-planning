from z3 import *
import json

def main():
    cities = {0: "Bucharest", 1: "Lyon", 2: "Porto"}
    n_days = 16
    
    M = [Int('M_%d' % (i+1)) for i in range(n_days)]
    E = [Int('E_%d' % (i+1)) for i in range(n_days)]
    
    s = Solver()
    
    for i in range(n_days):
        s.add(And(M[i] >= 0, M[i] <= 2))
        s.add(And(E[i] >= 0, E[i] <= 2))
    
    for i in range(n_days - 1):
        s.add(E[i] == M[i+1])
    
    valid_flights = [(0, 1), (1, 0), (1, 2), (2, 1)]
    for i in range(n_days):
        flight_cond = Or([And(M[i] == a, E[i] == b) for (a, b) in valid_flights])
        s.add(If(M[i] != E[i], flight_cond, True))
    
    b_days = 0
    l_days = 0
    p_days = 0
    
    for i in range(n_days):
        b_days += If(M[i] == 0, 1, 0)
        l_days += If(M[i] == 1, 1, 0)
        p_days += If(M[i] == 2, 1, 0)
        
        b_days += If(And(E[i] == 0, M[i] != 0), 1, 0)
        l_days += If(And(E[i] == 1, M[i] != 1), 1, 0)
        p_days += If(And(E[i] == 2, M[i] != 2), 1, 0)
    
    s.add(b_days == 7)
    s.add(l_days == 7)
    s.add(p_days == 4)
    
    wedding_days = []
    for i in range(7):
        wedding_days.append(Or(M[i] == 0, E[i] == 0))
    s.add(Or(wedding_days))
    
    if s.check() == sat:
        model = s.model()
        M_vals = [model.evaluate(M[i]).as_long() for i in range(n_days)]
        E_vals = [model.evaluate(E[i]).as_long() for i in range(n_days)]
        
        # Build the itinerary per day
        daily_places = []
        for i in range(n_days):
            if M_vals[i] == E_vals[i]:
                daily_places.append(cities[M_vals[i]])
            else:
                daily_places.append(cities[M_vals[i]] + " and " + cities[E_vals[i]])
        
        # Create segments with flight days included in both city stays
        segments = []
        current_place = daily_places[0]
        start_day = 1
        current_city = M_vals[0]  # Track primary city for segment
        
        for day in range(1, n_days):
            # Check for city continuation (considering flight days)
            current_city_continues = (
                current_place == daily_places[day] or 
                daily_places[day].startswith(cities[current_city] + " and") or 
                (daily_places[day].endswith(" and " + cities[current_city]) and 
                 " and " in daily_places[day])
            )
            
            if not current_city_continues:
                end_day = day
                segments.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities[current_city]
                })
                start_day = day + 1
                current_place = daily_places[day]
                current_city = M_vals[day]  # Reset to morning city
            else:
                current_place = daily_places[day]
        
        segments.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": cities[current_city]
        })
        
        # Output the itinerary
        result = {"itinerary": segments}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()