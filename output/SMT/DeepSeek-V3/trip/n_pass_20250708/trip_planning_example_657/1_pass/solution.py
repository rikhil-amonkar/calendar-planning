from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Frankfurt": 4,
        "Manchester": 4,
        "Valencia": 4,
        "Naples": 4,
        "Oslo": 3,
        "Vilnius": 2
    }
    
    # Direct flights: adjacency list
    flights = {
        "Valencia": ["Frankfurt", "Naples"],
        "Manchester": ["Frankfurt", "Naples", "Oslo"],
        "Naples": ["Manchester", "Frankfurt", "Oslo", "Valencia"],
        "Oslo": ["Naples", "Frankfurt", "Vilnius", "Manchester"],
        "Vilnius": ["Frankfurt", "Oslo"],
        "Frankfurt": ["Valencia", "Manchester", "Naples", "Oslo", "Vilnius"]
    }
    
    # Total days
    total_days = 16
    
    # Create a Z3 model for each day's city.
    s = Solver()
    
    # Day 1 to 16 (1-based)
    day_city = [Int(f"day_{i}_city") for i in range(1, 17)]
    
    # Map city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Each day's city must be one of the 6 cities
    for day in day_city:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Frankfurt must be days 13-16
    for day in range(13, 17):
        s.add(day_city[day - 1] == city_ids["Frankfurt"])
    
    # Wedding in Vilnius between day 12 and 13: so Vilnius must be day 12 (since day 13 is Frankfurt)
    s.add(day_city[11] == city_ids["Vilnius"])  # day 12 is index 11
    
    # Flight transitions: consecutive different cities must have a flight
    for i in range(15):  # days 1..15 to days 2..16
        current_city = day_city[i]
        next_city = day_city[i + 1]
        # If cities are different, check flight exists
        s.add(Implies(current_city != next_city, 
                      Or([And(current_city == city_ids[city1], next_city == city_ids[city2]) 
                          for city1 in flights 
                          for city2 in flights[city1]])))
    
    # Count days per city
    for city in cities:
        count = Sum([If(day_city[i] == city_ids[city], 1, 0) for i in range(16)])
        s.add(count == cities[city])
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Get the sequence of cities
        sequence = [id_to_city[m.evaluate(day_city[i]).as_long()] for i in range(16)]
        
        # Generate the itinerary
        itinerary = []
        current_city = sequence[0]
        start_day = 1
        
        for day in range(1, 16):
            if sequence[day] != sequence[day - 1]:
                # Flight day: add the stay up to the previous day, then the flight
                end_day = day  # the day of flight is day (1-based)
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
                # Add the flight day entries
                itinerary.append({"day_range": f"Day {day + 1}", "place": current_city})  # departure
                itinerary.append({"day_range": f"Day {day + 1}", "place": sequence[day]})  # arrival
                current_city = sequence[day]
                start_day = day + 1
        # Add the last stay
        end_day = 16
        if start_day <= end_day:
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)