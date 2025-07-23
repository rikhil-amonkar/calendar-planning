from z3 import *

def solve_itinerary():
    # Cities: 1 = Frankfurt, 2 = Krakow, 3 = Dubrovnik
    s = Solver()
    
    # Create variables for each day (1..10), each can be 1, 2, or 3
    days = [Int(f"day_{i}") for i in range(1, 11)]
    for day in days:
        s.add(Or(day == 1, day == 2, day == 3))
    
    # Constraint: Days 9 and 10 must be in Krakow (wedding)
    s.add(days[8] == 2)  # day 9
    s.add(days[9] == 2)  # day 10
    
    # Calculate days spent in each city
    frankfurt_days = Sum([If(day == 1, 1, 0) for day in days])
    krakow_days = Sum([If(day == 2, 1, 0) for day in days])
    dubrovnik_days = Sum([If(day == 3, 1, 0) for day in days])
    
    s.add(frankfurt_days == 3)
    s.add(krakow_days == 2)
    s.add(dubrovnik_days == 7)
    
    # Flight constraints: transitions must be between connected cities
    for i in range(9):  # days 1..9 transitioning to next day
        current = days[i]
        next_day = days[i+1]
        # Allowed transitions:
        # Frankfurt <-> Krakow
        # Frankfurt <-> Dubrovnik
        s.add(
            Or(
                current == next_day,  # stay in the same city
                And(current == 1, next_day == 2),  # F -> K
                And(current == 2, next_day == 1),  # K -> F
                And(current == 1, next_day == 3),  # F -> D
                And(current == 3, next_day == 1),  # D -> F
            )
        )
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(10):
            day_num = i + 1
            city_val = model.eval(days[i]).as_long()
            if city_val == 1:
                city = "Frankfurt"
            elif city_val == 2:
                city = "Krakow"
            else:
                city = "Dubrovnik"
            itinerary.append({"day": day_num, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))