from z3 import *
import json

def solve_itinerary():
    # Cities and their required stay days
    cities = {
        "Oslo": 5,
        "Stuttgart": 5,
        "Reykjavik": 2,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3,
        "Tallinn": 5,
        "Stockholm": 3
    }
    
    # Direct flights: key is source, value is list of destinations
    direct_flights = {
        "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn", "Oslo"],
        "Stockholm": ["Oslo", "Stuttgart", "Split", "Geneva", "Reykjavik"],
        "Stuttgart": ["Porto", "Stockholm", "Split"],
        "Oslo": ["Split", "Geneva", "Porto", "Stockholm", "Tallinn", "Reykjavik"],
        "Split": ["Stuttgart", "Oslo", "Geneva", "Stockholm"],
        "Geneva": ["Porto", "Split", "Oslo", "Stockholm"],
        "Porto": ["Stuttgart", "Geneva", "Oslo"],
        "Tallinn": ["Oslo", "Reykjavik"]
    }
    
    # Total days
    total_days = 21
    days = range(1, total_days + 1)
    
    # Z3 variables: day[i] is the city on day i (1-based)
    day_vars = [Int(f"day_{i}") for i in days]
    
    # City to integer mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day variable must be a valid city id
    for d in day_vars:
        s.add(And(d >= 0, d < len(cities)))
    
    # Fixed constraints:
    # Reykjavik on day 1 and 2
    s.add(day_vars[0] == city_ids["Reykjavik"])
    s.add(day_vars[1] == city_ids["Reykjavik"])
    
    # Porto between day 19-21 (indices 18-20)
    s.add(day_vars[18] == city_ids["Porto"])
    s.add(day_vars[19] == city_ids["Porto"])
    s.add(day_vars[20] == city_ids["Porto"])
    
    # Stockholm between day 2 and 4 (indices 1-3)
    # Must have at least one day in Stockholm during days 2-4
    stockholm_days = [day_vars[i] == city_ids["Stockholm"] for i in range(1, 4)]
    s.add(Or(stockholm_days))
    
    # Flight transitions: consecutive days must be connected by a direct flight or same city
    for i in range(total_days - 1):
        current = day_vars[i]
        next_ = day_vars[i + 1]
        # Either stay in same city or fly to connected city
        same_city = current == next_
        # Generate all possible flight connections
        flight_options = []
        for src in direct_flights:
            for dst in direct_flights[src]:
                flight_options.append(And(current == city_ids[src], next_ == city_ids[dst]))
        s.add(Or(same_city, *flight_options))
    
    # Duration constraints: each city must be visited for exactly the required days
    for city, required_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day_vars[i] == city_id, 1, 0) for i in range(total_days)) == required_days)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        # Generate the day sequence from the model
        day_sequence = []
        for i in range(total_days):
            city_id = model.evaluate(day_vars[i]).as_long()
            day_sequence.append(id_to_city[city_id])
        
        # Process the day sequence to create the itinerary
        current_place = day_sequence[0]
        start_day = 1
        for day in range(1, total_days):
            if day_sequence[day] != current_place:
                # Add the stay up to previous day
                if start_day == day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_place})
                # Add the transition day
                itinerary.append({"day_range": f"Day {day + 1}", "place": current_place})
                itinerary.append({"day_range": f"Day {day + 1}", "place": day_sequence[day]})
                current_place = day_sequence[day]
                start_day = day + 1
        
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))