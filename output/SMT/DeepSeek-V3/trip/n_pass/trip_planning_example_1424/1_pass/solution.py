from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Porto": 5,
        "Amsterdam": 4,
        "Helsinki": 4,
        "Naples": 4,
        "Brussels": 3,
        "Warsaw": 3,
        "Split": 3,
        "Reykjavik": 5,
        "Lyon": 3,
        "Valencia": 2
    }
    
    # Fixed events
    fixed_events = [
        ("Porto", 1, 5),
        ("Amsterdam", 5, 8),
        ("Helsinki", 8, 11),
        ("Naples", 17, 20),
        ("Brussels", 20, 22)
    ]
    
    # Direct flights
    direct_flights = {
        "Amsterdam": ["Warsaw", "Lyon", "Naples", "Reykjavik", "Split", "Helsinki", "Valencia"],
        "Helsinki": ["Brussels", "Warsaw", "Reykjavik", "Split", "Naples"],
        "Reykjavik": ["Brussels", "Warsaw", "Helsinki"],
        "Brussels": ["Helsinki", "Reykjavik", "Lyon", "Valencia"],
        "Lyon": ["Amsterdam", "Split", "Brussels", "Valencia"],
        "Naples": ["Amsterdam", "Valencia", "Split", "Brussels", "Warsaw"],
        "Porto": ["Brussels", "Amsterdam", "Lyon", "Warsaw", "Valencia"],
        "Split": ["Amsterdam", "Lyon", "Warsaw", "Helsinki", "Naples"],
        "Warsaw": ["Amsterdam", "Helsinki", "Reykjavik", "Split", "Brussels", "Naples", "Valencia"],
        "Valencia": ["Naples", "Brussels", "Lyon", "Warsaw", "Amsterdam", "Porto"]
    }
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables: for each day (1-27), the city visited
    days = 27
    city_list = list(cities.keys())
    day_to_city = [Int(f"day_{day}") for day in range(1, days + 1)]
    for day in range(days):
        s.add(day_to_city[day] >= 0, day_to_city[day] < len(city_list))
    
    # Fixed events constraints
    for city, start, end in fixed_events:
        city_idx = city_list.index(city)
        for day in range(start - 1, end):
            s.add(day_to_city[day] == city_idx)
    
    # Duration constraints
    for city, duration in cities.items():
        city_idx = city_list.index(city)
        s.add(Sum([If(day_to_city[day] == city_idx, 1, 0) for day in range(days)]) == duration)
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for day in range(days - 1):
        current_city_idx = day_to_city[day]
        next_city_idx = day_to_city[day + 1]
        current_city = city_list[current_city_idx]
        next_city = city_list[next_city_idx]
        s.add(Or(
            current_city_idx == next_city_idx,
            And(current_city in direct_flights, next_city in direct_flights[current_city])
        ))
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Generate the sequence of cities
        sequence = []
        for day in range(days):
            city_idx = model.evaluate(day_to_city[day]).as_long()
            sequence.append(city_list[city_idx])
        
        # Generate the itinerary with day ranges
        current_city = sequence[0]
        start_day = 1
        for day in range(1, days):
            if sequence[day] != sequence[day - 1]:
                # End of stay in current_city
                itinerary.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": current_city
                })
                # Flight day: day is in both current_city and next city
                itinerary.append({
                    "day_range": f"Day {day}",
                    "place": current_city
                })
                itinerary.append({
                    "day_range": f"Day {day}",
                    "place": sequence[day]
                })
                current_city = sequence[day]
                start_day = day + 1
        # Add the last segment
        itinerary.append({
            "day_range": f"Day {start_day}-{days}",
            "place": current_city
        })
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))