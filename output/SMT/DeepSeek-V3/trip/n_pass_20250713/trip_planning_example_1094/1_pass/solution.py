from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Vienna": 4,
        "Barcelona": 2,
        "Edinburgh": 4,
        "Krakow": 3,
        "Riga": 4,
        "Hamburg": 2,
        "Paris": 2,
        "Stockholm": 2
    }
    
    # Direct flights as a dictionary: key is source, value is list of destinations
    direct_flights = {
        "Hamburg": ["Stockholm", "Vienna", "Paris", "Barcelona", "Edinburgh"],
        "Vienna": ["Stockholm", "Hamburg", "Barcelona", "Krakow", "Paris", "Riga"],
        "Paris": ["Edinburgh", "Riga", "Krakow", "Stockholm", "Hamburg", "Barcelona", "Vienna"],
        "Riga": ["Barcelona", "Paris", "Edinburgh", "Stockholm", "Hamburg"],
        "Krakow": ["Barcelona", "Stockholm", "Edinburgh", "Paris", "Vienna"],
        "Barcelona": ["Riga", "Krakow", "Stockholm", "Edinburgh", "Paris", "Hamburg", "Vienna"],
        "Edinburgh": ["Paris", "Stockholm", "Riga", "Barcelona", "Hamburg", "Krakow"],
        "Stockholm": ["Hamburg", "Vienna", "Paris", "Riga", "Krakow", "Barcelona", "Edinburgh"]
    }
    
    # Fixed events
    fixed_events = [
        ("Paris", 1, 2),   # Wedding in Paris on days 1-2
        ("Hamburg", 10, 11), # Conference in Hamburg on days 10-11
        ("Edinburgh", 12, 15), # Meet friend in Edinburgh between days 12-15 (must be there at least one day in this range)
        ("Stockholm", 15, 16) # Visit relatives in Stockholm between days 15-16
    ]
    
    # Initialize Z3 solver
    s = Solver()
    
    # Variables: for each day, which city are you in?
    day_city = [Int(f"day_{i}_city") for i in range(1, 17)]
    
    # Assign each city a unique integer
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraint: each day_city variable must be a valid city ID
    for day in day_city:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Fixed events constraints
    for city, start_day, end_day in fixed_events:
        for day in range(start_day, end_day + 1):
            s.add(day_city[day - 1] == city_ids[city])
    
    # Duration constraints: each city must be visited for exactly the required days
    for city, req_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day_city[i] == city_id, 1, 0) for i in range(16)]) == req_days)
    
    # Flight constraints: consecutive days must be the same city or connected by a direct flight
    for i in range(15):
        current_day = day_city[i]
        next_day = day_city[i + 1]
        # Either stay in the same city or fly to a connected city
        s.add(Or(
            current_day == next_day,
            And(
                current_day != next_day,
                Or([And(current_day == city_ids[src], next_day == city_ids[dst]) 
                    for src in direct_flights 
                    for dst in direct_flights[src]])
            )
        ))
    
    # Additional constraints for Edinburgh meet (must be there at least one day between 12-15)
    s.add(Or([day_city[i] == city_ids["Edinburgh"] for i in range(11, 15)]))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Determine the sequence of cities from the model
        sequence = []
        for i in range(16):
            city_id = model.evaluate(day_city[i]).as_long()
            sequence.append(id_to_city[city_id])
        
        # Generate the itinerary with day ranges and flight days
        current_city = sequence[0]
        start_day = 1
        
        for i in range(1, 16):
            if sequence[i] != sequence[i-1]:
                # Flight day: i is the day of transition
                end_day = i
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
                    itinerary.append({"day_range": f"Day {end_day}", "place": current_city})
                # The next city starts on the same day
                itinerary.append({"day_range": f"Day {end_day}", "place": sequence[i]})
                current_city = sequence[i]
                start_day = end_day + 1 if end_day + 1 <= 16 else 16
        # Add the last segment
        if start_day <= 16:
            if start_day == 16:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-16", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))