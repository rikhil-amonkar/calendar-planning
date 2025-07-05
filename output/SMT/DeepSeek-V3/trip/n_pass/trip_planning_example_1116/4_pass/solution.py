from z3 import *
import json

def solve_itinerary():
    # Cities involved
    cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}
    
    # Direct flights
    direct_flights = {
        "Reykjavik": ["Munich", "Oslo", "Frankfurt", "Barcelona", "Stockholm"],
        "Munich": ["Reykjavik", "Frankfurt", "Bucharest", "Oslo", "Stockholm", "Barcelona", "Split"],
        "Frankfurt": ["Munich", "Oslo", "Barcelona", "Reykjavik", "Bucharest", "Stockholm", "Split"],
        "Oslo": ["Split", "Reykjavik", "Frankfurt", "Bucharest", "Stockholm", "Barcelona", "Munich"],
        "Bucharest": ["Munich", "Barcelona", "Oslo", "Frankfurt"],
        "Barcelona": ["Bucharest", "Frankfurt", "Reykjavik", "Stockholm", "Split", "Oslo", "Munich"],
        "Stockholm": ["Barcelona", "Reykjavik", "Munich", "Oslo", "Frankfurt", "Split"],
        "Split": ["Oslo", "Barcelona", "Stockholm", "Frankfurt", "Munich"]
    }
    
    # Required days per city
    required_days = {
        "Oslo": 2,
        "Reykjavik": 5,
        "Stockholm": 4,
        "Munich": 4,
        "Frankfurt": 4,
        "Barcelona": 3,
        "Bucharest": 2,
        "Split": 3
    }
    
    total_days = 20
    
    # Create Z3 solver
    s = Solver()
    
    # day_to_city[d] is the city visited on day d (1-based)
    day_to_city = [Int(f"day_{d}") for d in range(1, total_days + 1)]
    
    # Each day's city is a valid city
    for day in day_to_city:
        s.add(day >= 0, day < len(cities))
    
    # Total days per city matches required_days
    for city in cities:
        city_int = city_to_int[city]
        s.add(Sum([If(day == city_int, 1, 0) for day in day_to_city]) == required_days[city])
    
    # Specific constraints:
    # Oslo on days 16 and 17 (1-based)
    oslo_int = city_to_int["Oslo"]
    s.add(day_to_city[15] == oslo_int)  # Day 16
    s.add(day_to_city[16] == oslo_int)  # Day 17
    
    # Reykjavik between days 9-13 (indices 8-12 in 0-based)
    reykjavik_int = city_to_int["Reykjavik"]
    s.add(Or([day_to_city[d] == reykjavik_int for d in range(8, 13)]))
    
    # Munich between days 13-16 (indices 12-15 in 0-based)
    munich_int = city_to_int["Munich"]
    s.add(Or([day_to_city[d] == munich_int for d in range(12, 16)]))
    
    # Frankfurt between days 17-20 (indices 16-19 in 0-based)
    frankfurt_int = city_to_int["Frankfurt"]
    s.add(Or([day_to_city[d] == frankfurt_int for d in range(16, 20)]))
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(total_days - 1):
        current_day = day_to_city[i]
        next_day = day_to_city[i + 1]
        # Either same city or direct flight exists
        s.add(Or(
            current_day == next_day,
            And(current_day != next_day, 
                Or([And(current_day == city_to_int[city], 
                        next_day == city_to_int[neighbor])
                    for city in cities 
                    for neighbor in direct_flights.get(city, [])]))
        ))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Extract the city sequence
        city_sequence = [int_to_city[m.evaluate(day).as_long()] for day in day_to_city]
        
        # Generate the itinerary with flight days handled
        itinerary = []
        current_city = city_sequence[0]
        start_day = 1
        for day in range(1, total_days + 1):
            if day == 1:
                continue
            if city_sequence[day - 1] != city_sequence[day - 2]:
                # Flight day: day is in both cities
                itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city_sequence[day - 2]})
                itinerary.append({"day_range": f"Day {day}", "place": city_sequence[day - 1]})
                start_day = day
                current_city = city_sequence[day - 1]
        # Add the last stretch
        itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        # Now, merge consecutive same-city entries
        merged_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            current = itinerary[i]
            if i + 1 < n and current["place"] == itinerary[i + 1]["place"]:
                # Merge them
                start = current["day_range"].split('-')[0].replace("Day ", "")
                end = itinerary[i + 1]["day_range"].split('-')[-1].replace("Day ", "")
                merged_entry = {"day_range": f"Day {start}-{end}", "place": current["place"]}
                merged_itinerary.append(merged_entry)
                i += 2
            else:
                merged_itinerary.append(current)
                i += 1
        
        return {"itinerary": merged_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))