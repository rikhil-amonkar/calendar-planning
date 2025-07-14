from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4
    }
    
    # Direct flight connections (undirected)
    direct_flights = {
        "Paris": ["Krakow", "Amsterdam", "Split", "Geneva", "Budapest", "Vilnius", "Munich"],
        "Krakow": ["Paris", "Split", "Munich", "Amsterdam", "Vilnius"],
        "Vilnius": ["Munich", "Split", "Amsterdam", "Paris", "Krakow"],
        "Munich": ["Vilnius", "Split", "Amsterdam", "Geneva", "Krakow", "Paris", "Budapest"],
        "Geneva": ["Paris", "Amsterdam", "Split", "Munich", "Budapest", "Santorini"],
        "Amsterdam": ["Paris", "Geneva", "Munich", "Budapest", "Split", "Vilnius", "Krakow", "Santorini"],
        "Budapest": ["Amsterdam", "Paris", "Geneva", "Munich"],
        "Split": ["Paris", "Munich", "Geneva", "Amsterdam", "Krakow", "Vilnius"],
        "Santorini": ["Geneva", "Amsterdam"]
    }
    
    # Create a solver instance
    s = Solver()
    
    # Days are from 1 to 30
    days = 30
    
    # Assign a city to each day
    city_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Create a mapping from city names to integers
    city_map = {city: idx for idx, city in enumerate(cities.keys())}
    city_inv_map = {idx: city for city, idx in city_map.items()}
    
    # Constraints: each day's city_var must be within 0..8 (for 9 cities)
    for day in range(days):
        s.add(city_vars[day] >= 0, city_vars[day] < len(cities))
    
    # Constraints for the required stays and specific date ranges
    # Santorini: 5 days total, with some days between 25-29
    santorini_idx = city_map["Santorini"]
    s.add(Sum([If(city_vars[i] == santorini_idx, 1, 0) for i in range(days)]) == 5)
    s.add(Or([city_vars[i] == santorini_idx for i in range(24, 29)]))  # days 25-29 (indices 24-28)
    
    # Krakow: 5 days total, wedding between day 18-22
    krakow_idx = city_map["Krakow"]
    s.add(Sum([If(city_vars[i] == krakow_idx, 1, 0) for i in range(days)]) == 5)
    s.add(Or([city_vars[i] == krakow_idx for i in range(17, 22)]))  # days 18-22 (indices 17-21)
    
    # Paris: 5 days total, meet friend between day 11-15
    paris_idx = city_map["Paris"]
    s.add(Sum([If(city_vars[i] == paris_idx, 1, 0) for i in range(days)]) == 5)
    s.add(Or([city_vars[i] == paris_idx for i in range(10, 15)]))  # days 11-15 (indices 10-14)
    
    # Other cities: exact day counts
    vilnius_idx = city_map["Vilnius"]
    s.add(Sum([If(city_vars[i] == vilnius_idx, 1, 0) for i in range(days)]) == 3)
    
    munich_idx = city_map["Munich"]
    s.add(Sum([If(city_vars[i] == munich_idx, 1, 0) for i in range(days)]) == 5)
    
    geneva_idx = city_map["Geneva"]
    s.add(Sum([If(city_vars[i] == geneva_idx, 1, 0) for i in range(days)]) == 2)
    
    amsterdam_idx = city_map["Amsterdam"]
    s.add(Sum([If(city_vars[i] == amsterdam_idx, 1, 0) for i in range(days)]) == 4)
    
    budapest_idx = city_map["Budapest"]
    s.add(Sum([If(city_vars[i] == budapest_idx, 1, 0) for i in range(days)]) == 5)
    
    split_idx = city_map["Split"]
    s.add(Sum([If(city_vars[i] == split_idx, 1, 0) for i in range(days)]) == 4)
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(days - 1):
        current_city = city_vars[i]
        next_city = city_vars[i + 1]
        # If cities are different, ensure there's a direct flight
        s.add(Implies(current_city != next_city, 
                      Or([And(current_city == city_map[c1], next_city == city_map[c2]) 
                          for c1 in direct_flights 
                          for c2 in direct_flights[c1]])))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        day_sequence = []
        for day in range(days):
            city_idx = m.evaluate(city_vars[day]).as_long()
            city = city_inv_map[city_idx]
            day_sequence.append((day + 1, city))  # days are 1-based
        
        # Process day_sequence to create itinerary with ranges and flight days
        itinerary = []
        i = 0
        n = len(day_sequence)
        while i < n:
            start_day, city = day_sequence[i]
            j = i
            while j < n and day_sequence[j][1] == city:
                j += 1
            end_day = day_sequence[j-1][0]
            # Add the stay entry
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            # Check if there's a next city
            if j < n:
                # The transition day is day_sequence[j][0] (the first day of the next city)
                transition_day = day_sequence[j][0]
                next_city = day_sequence[j][1]
                # Add departure and arrival entries
                itinerary.append({"day_range": f"Day {transition_day}", "place": city})
                itinerary.append({"day_range": f"Day {transition_day}", "place": next_city})
            i = j
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))