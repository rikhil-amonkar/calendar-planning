from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Dublin", "London", "Hamburg", "Helsinki", "Reykjavik", "Mykonos"]
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        "Dublin": ["London", "Hamburg", "Helsinki", "Reykjavik"],
        "London": ["Dublin", "Hamburg", "Reykjavik", "Mykonos"],
        "Hamburg": ["Dublin", "London", "Helsinki"],
        "Helsinki": ["Hamburg", "Reykjavik", "London", "Dublin"],
        "Reykjavik": ["Helsinki", "London", "Dublin"],
        "Mykonos": ["London"]
    }
    
    # Create solver
    s = Solver()
    
    # Variables: day_1 to day_16, each is an integer representing city index
    days = [Int(f"day_{i}") for i in range(1, 17)]
    
    # Each day variable must be between 0 and 5 (inclusive)
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(1, 16):
        current_city = days[i-1]
        next_city = days[i]
        # Either stay in the same city or move to a directly connected city
        same_city = (current_city == next_city)
        current_city_name = cities[current_city]
        flight_possible = Or([next_city == city_indices[neighbor] 
                            for neighbor in direct_flights[current_city_name]])
        s.add(Or(same_city, flight_possible))
    
    # Duration constraints
    def city_days(city_name):
        return Sum([If(days[i] == city_indices[city_name], 1, 0) for i in range(16)])
    
    s.add(city_days("Dublin") == 5)
    s.add(city_days("London") == 5)
    s.add(city_days("Hamburg") == 2)
    s.add(city_days("Helsinki") == 4)
    s.add(city_days("Reykjavik") == 2)
    s.add(city_days("Mykonos") == 3)
    
    # Event constraints
    # Wedding in Reykjavik between day 9 and 10: at least one of day 9 or 10 is Reykjavik
    s.add(Or(days[8] == city_indices["Reykjavik"], days[9] == city_indices["Reykjavik"]))
    
    # Show in Dublin from day 2 to 6 (days 2,3,4,5,6 in 1-based)
    for i in range(1, 6):  # days 2-6 (indices 1 to 5 in 0-based)
        s.add(days[i] == city_indices["Dublin"])
    
    # Meet friends in Hamburg between day 1 and 2 (days 1 or 2)
    s.add(Or(days[0] == city_indices["Hamburg"], days[1] == city_indices["Hamburg"]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        for day in range(1, 17):
            city_idx = m.evaluate(days[day-1]).as_long()
            city = cities[city_idx]
            if current_place is None:
                current_place = city
                start_day = day
            elif city != current_place:
                # Add the previous stay
                if start_day == day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_place})
                # Add the flight day entries for the previous and new city
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_place = city
                start_day = day
        # Add the last stay
        if start_day == 16:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-16", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(result)