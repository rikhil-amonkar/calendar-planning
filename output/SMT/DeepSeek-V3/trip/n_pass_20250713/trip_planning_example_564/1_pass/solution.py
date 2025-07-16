from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Istanbul", "Rome", "Seville", "Naples", "Santorini"]
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        "Rome": ["Santorini", "Seville", "Naples", "Istanbul"],
        "Santorini": ["Rome", "Naples"],
        "Seville": ["Rome"],
        "Naples": ["Istanbul", "Santorini", "Rome"],
        "Istanbul": ["Naples", "Rome"]
    }
    
    # Days
    num_days = 16
    days = list(range(1, num_days + 1))
    
    # Create Z3 variables: for each day, which city are we in?
    day_to_city = [Int(f"day_{day}_city") for day in days]
    
    s = Solver()
    
    # Each day's city must be one of the 5 cities (0 to 4)
    for day in days:
        s.add(And(day_to_city[day-1] >= 0, day_to_city[day-1] < 5))
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for day in range(1, num_days):
        current_city = day_to_city[day-1]
        next_city = day_to_city[day]
        # Either stay in the same city, or move to a connected city
        s.add(Or(
            current_city == next_city,
            # Check if there's a direct flight
            *[And(current_city == city_map[city1], next_city == city_map[city2]) 
              for city1 in direct_flights 
              for city2 in direct_flights[city1]]
        ))
    
    # Duration constraints
    # Istanbul: 2 days
    istanbul_days = Sum([If(day_to_city[day-1] == city_map["Istanbul"], 1, 0) for day in days])
    s.add(istanbul_days == 2)
    
    # Rome: 3 days
    rome_days = Sum([If(day_to_city[day-1] == city_map["Rome"], 1, 0) for day in days])
    s.add(rome_days == 3)
    
    # Seville: 4 days
    seville_days = Sum([If(day_to_city[day-1] == city_map["Seville"], 1, 0) for day in days])
    s.add(seville_days == 4)
    
    # Naples: 7 days
    naples_days = Sum([If(day_to_city[day-1] == city_map["Naples"], 1, 0) for day in days])
    s.add(naples_days == 7)
    
    # Santorini: 4 days
    santorini_days = Sum([If(day_to_city[day-1] == city_map["Santorini"], 1, 0) for day in days])
    s.add(santorini_days == 4)
    
    # Event constraints
    # Istanbul between day 6 and 7 (i.e., day 6 or 7 must be Istanbul)
    s.add(Or(day_to_city[5] == city_map["Istanbul"], day_to_city[6] == city_map["Istanbul"]))
    
    # Santorini between day 13 and 16 (i.e., at least one of days 13-16 is Santorini)
    s.add(Or([day_to_city[day-1] == city_map["Santorini"] for day in range(13, 17)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        # Helper function to get city name from index
        def get_city(idx):
            return cities[idx]
        
        # Generate the itinerary
        for day in days:
            city_idx = model.evaluate(day_to_city[day-1]).as_long()
            city = get_city(city_idx)
            
            if day == 1:
                current_place = city
                start_day = 1
            else:
                if city != current_place:
                    # Add the previous stay
                    if start_day == day - 1:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_place})
                    # Add the flight day records for both departure and arrival
                    itinerary.append({"day_range": f"Day {day}", "place": current_place})
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                    # Update current place and start day
                    current_place = city
                    start_day = day
                # else: continue the same city
        
        # Add the last stay
        if start_day == num_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{num_days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Correcting the direct_flights variable name (it was misspelled as direct_flights earlier)
direct_flights = {
    "Rome": ["Santorini", "Seville", "Naples", "Istanbul"],
    "Santorini": ["Rome", "Naples"],
    "Seville": ["Rome"],
    "Naples": ["Istanbul", "Santorini", "Rome"],
    "Istanbul": ["Naples", "Rome"]
}

# Execute the function
result = solve_itinerary()
print(result)