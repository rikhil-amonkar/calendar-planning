from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Reykjavik": 7,
        "Riga": 2,
        "Warsaw": 3,
        "Istanbul": 6,
        "Krakow": 7
    }
    city_list = list(cities.keys())
    
    # Direct flights as adjacency list
    direct_flights = {
        "Istanbul": ["Krakow", "Warsaw", "Riga"],
        "Krakow": ["Istanbul", "Warsaw"],
        "Warsaw": ["Istanbul", "Krakow", "Reykjavik", "Riga"],
        "Riga": ["Istanbul", "Warsaw"],
        "Reykjavik": ["Warsaw"]
    }
    
    # Total days
    total_days = 21
    
    # Create a solver instance
    s = Solver()
    
    # Variables: for each day (1..21), which city are we in?
    day_to_city = [Int(f"day_{i}_city") for i in range(1, total_days + 1)]
    
    # Map city names to integer indices
    city_index = {city: idx for idx, city in enumerate(city_list)}
    
    # Constraints: each day's city must be one of the five cities
    for day_var in day_to_city:
        s.add(Or([day_var == city_index[city] for city in city_list]))
    
    # Constraints for transitions: consecutive days must be either same city or connected by direct flight
    for i in range(total_days - 1):
        current_city = day_to_city[i]
        next_city = day_to_city[i + 1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_index[c1], next_city == city_index[c2])
                for c1 in city_list for c2 in direct_flights[c1]
            ]
        ))
    
    # Constraints for total days in each city
    for city in city_list:
        count = 0
        for day_var in day_to_city:
            count += If(day_var == city_index[city], 1, 0)
        s.add(count == cities[city])
    
    # Special constraints:
    # Wedding in Istanbul between day 2 and 7: so Istanbul must include at least one day in 2-7.
    s.add(Or([day_to_city[i] == city_index["Istanbul"] for i in range(1, 7)]))  # days 2-7 are indices 1..6 (0-based)
    
    # Meeting in Riga between day 1 and 2: so Riga must be on day 1 or 2.
    s.add(Or(day_to_city[0] == city_index["Riga"], day_to_city[1] == city_index["Riga"]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Generate the day-to-city sequence
        sequence = []
        for day in range(total_days):
            city_idx = model.evaluate(day_to_city[day]).as_long()
            city = city_list[city_idx]
            sequence.append((day + 1, city))  # (day_number, city)
        
        # Process the sequence into the itinerary format
        itinerary = []
        i = 0
        n = len(sequence)
        while i < n:
            current_day, current_city = sequence[i]
            j = i
            while j < n and sequence[j][1] == current_city:
                j += 1
            start_day = sequence[i][0]
            end_day = sequence[j-1][0]
            if start_day == end_day:
                day_str = f"Day {start_day}"
            else:
                day_str = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_str, "place": current_city})
            # Check if this is followed by a different city (flight day)
            if j < n:
                next_day, next_city = sequence[j][0], sequence[j][1]
                # The flight occurs on end_day (last day of current city)
                # Add entries for the flight day
                itinerary.append({"day_range": f"Day {end_day}", "place": current_city})
                itinerary.append({"day_range": f"Day {end_day}", "place": next_city})
            i = j
        
        # Prepare the output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))