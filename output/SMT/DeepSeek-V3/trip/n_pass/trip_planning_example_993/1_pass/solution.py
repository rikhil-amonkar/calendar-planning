import json
from z3 import *

def solve_itinerary():
    cities = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,
        "Vilnius": 5,
        "London": 2,
        "Stockholm": 3,
        "Bucharest": 4
    }
    
    direct_flights = {
        "London": ["Amsterdam", "Bucharest", "Frankfurt", "Stockholm"],
        "Amsterdam": ["London", "Stockholm", "Frankfurt", "Riga", "Bucharest", "Vilnius"],
        "Vilnius": ["Frankfurt", "Riga", "Amsterdam"],
        "Frankfurt": ["Vilnius", "Riga", "Amsterdam", "Stockholm", "Bucharest", "London"],
        "Riga": ["Vilnius", "Stockholm", "Frankfurt", "Bucharest", "Amsterdam"],
        "Stockholm": ["Riga", "Amsterdam", "Frankfurt", "London"],
        "Bucharest": ["London", "Riga", "Frankfurt", "Amsterdam"]
    }
    
    total_days = 15
    
    # Create Z3 variables for each day (1-based)
    days = [Int(f"day_{i+1}") for i in range(total_days)]
    
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraints for required days per city
    for city, required_days in cities.items():
        s.add(Sum([If(day == city_ids[city], 1, 0) for day in days]) == required_days)
    
    # Flight constraints: consecutive days must be connected by direct flights
    for i in range(total_days - 1):
        current_day = days[i]
        next_day = days[i + 1]
        s.add(Or([And(current_day == city_ids[c1], next_day == city_ids[c2]) 
                  for c1 in direct_flights 
                  for c2 in direct_flights[c1]]))
    
    # Specific constraints
    # Amsterdam friend meeting between day 2 and 3 (so day 2 or 3 must be Amsterdam)
    s.add(Or(days[1] == city_ids["Amsterdam"], days[2] == city_ids["Amsterdam"]))
    
    # Vilnius workshop between day 7 and 11 (indices 6 to 10)
    s.add(Or([days[i] == city_ids["Vilnius"] for i in range(6, 11)]))
    
    # Stockholm wedding between day 13 and 15 (indices 12 to 14)
    s.add(Or([days[i] == city_ids["Stockholm"] for i in range(12, 15)]))
    
    if s.check() == sat:
        model = s.model()
        day_assignments = []
        for i in range(total_days):
            city_id = model.eval(days[i]).as_long()
            city = id_to_city[city_id]
            day_assignments.append(city)
        
        itinerary = []
        current_city = day_assignments[0]
        start_day = 1
        
        for i in range(1, total_days):
            if day_assignments[i] != day_assignments[i-1]:
                # End of stay in current_city
                end_day = i
                if start_day == end_day:
                    day_str = f"Day {start_day}"
                else:
                    day_str = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_str, "place": current_city})
                # Flight day: i+1 is the day of flight (since days are 1-based)
                flight_day = i + 1
                itinerary.append({"day_range": f"Day {flight_day}", "place": day_assignments[i-1]})
                itinerary.append({"day_range": f"Day {flight_day}", "place": day_assignments[i]})
                current_city = day_assignments[i]
                start_day = i + 1
        
        # Add the last stay
        end_day = total_days
        if start_day == end_day:
            day_str = f"Day {start_day}"
        else:
            day_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_str, "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found."}

itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))