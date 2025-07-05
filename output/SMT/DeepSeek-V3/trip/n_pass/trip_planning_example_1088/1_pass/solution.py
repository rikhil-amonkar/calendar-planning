from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
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
        "Stuttgart": ["Porto", "Split", "Reykjavik", "Stockholm"],
        "Oslo": ["Split", "Geneva", "Porto", "Stockholm", "Tallinn", "Reykjavik"],
        "Split": ["Stuttgart", "Oslo", "Geneva", "Stockholm"],
        "Geneva": ["Porto", "Split", "Oslo", "Stockholm"],
        "Tallinn": ["Oslo", "Reykjavik"],
        "Porto": ["Stuttgart", "Oslo", "Geneva"]
    }
    
    # Fixed events
    fixed_events = [
        ("Reykjavik", 1, 2),  # Days 1-2 in Reykjavik
        ("Porto", 19, 21),     # Days 19-21 in Porto
        ("Stockholm", 2, 4)     # Meet friend in Stockholm between day 2-4
    ]
    
    # Create a solver instance
    s = Solver()
    
    # Variables: day_1 to day_21, each can be one of the cities
    days = [Int(f"day_{i}") for i in range(1, 22)]
    city_list = list(cities.keys())
    for day in days:
        s.add(Or([day == i for i in range(len(city_list))]))
    
    # Map city names to indices
    city_index = {city: idx for idx, city in enumerate(city_list)}
    
    # Convert fixed events to constraints
    for city, start, end in fixed_events:
        idx = city_index[city]
        for day in range(start, end + 1):
            s.add(days[day - 1] == idx)
    
    # Constraint: Total days per city must match requirements
    for city, required_days in cities.items():
        idx = city_index[city]
        total = Sum([If(days[i] == idx, 1, 0) for i in range(21)])
        s.add(total == required_days)
    
    # Constraint: Flight transitions must be direct
    for i in range(20):  # days 1..20 can transition to next day
        current_day = days[i]
        next_day = days[i + 1]
        # Either stay in the same city or fly to a directly connected city
        same_city = current_day == next_day
        possible_flights = []
        for src in direct_flights:
            for dst in direct_flights[src]:
                if src in city_index and dst in city_index:
                    possible_flights.append(And(current_day == city_index[src], next_day == city_index[dst]))
        s.add(Or(same_city, Or(possible_flights)))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Generate the day sequence
        day_sequence = []
        for i in range(21):
            day_num = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            city = city_list[city_idx]
            day_sequence.append(city)
        
        # Generate the itinerary
        itinerary = []
        current_city = day_sequence[0]
        start_day = 1
        for day in range(1, 21):
            if day_sequence[day] != current_city:
                # Add the stay up to day
                if start_day == day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
                # Add the flight day (day+1)
                itinerary.append({"day_range": f"Day {day + 1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day + 1}", "place": day_sequence[day]})
                current_city = day_sequence[day]
                start_day = day + 2  # because day+1 is the flight day
        # Add the last stay
        if start_day <= 21:
            if start_day == 21:
                itinerary.append({"day_range": "Day 21", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-21", "place": current_city})
        
        # Now, handle the case where the flight is on the same day as the end of a stay
        # The above code may not capture all cases, so here's another approach:
        itinerary = []
        current_stay_start = 1
        for day in range(2, 22):
            if day_sequence[day - 1] != day_sequence[day - 2]:
                # Flight from day_sequence[day-2] to day_sequence[day-1] on day
                # Add the stay up to day-1
                if current_stay_start == day - 1:
                    itinerary.append({"day_range": f"Day {current_stay_start}", "place": day_sequence[day - 2]})
                else:
                    itinerary.append({"day_range": f"Day {current_stay_start}-{day - 1}", "place": day_sequence[day - 2]})
                # Add the flight day
                itinerary.append({"day_range": f"Day {day}", "place": day_sequence[day - 2]})
                itinerary.append({"day_range": f"Day {day}", "place": day_sequence[day - 1]})
                current_stay_start = day + 1
        # Add the last stay
        if current_stay_start <= 21:
            if current_stay_start == 21:
                itinerary.append({"day_range": "Day 21", "place": day_sequence[20]})
            else:
                itinerary.append({"day_range": f"Day {current_stay_start}-21", "place": day_sequence[20]})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))