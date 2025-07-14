from z3 import *

def solve_scheduling_problem():
    # Cities and their required days
    cities = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4
    }
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
        "Prague": ["Helsinki", "Valencia", "Reykjavik"],
        "Valencia": ["Prague", "Porto"],
        "Porto": ["Valencia"],
        "Reykjavik": ["Helsinki", "Prague"],
        "Dubrovnik": ["Helsinki"]
    }
    
    # Total days
    total_days = 18
    
    # Create Z3 variables: day[i] is the city visited on day i+1 (since days are 1-based)
    days = [Int(f"day_{i+1}") for i in range(total_days)]
    
    s = Solver()
    
    # Constraint: each day's value must be a valid city id
    for day in days:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraint: total days per city must match requirements
    for city, required_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(day == city_id, 1, 0) for day in days]) == required_days)
    
    # Constraint: transitions between cities must be direct flights
    for i in range(total_days - 1):
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_day == next_day,
            *[And(current_day == city_ids[city1], next_day == city_ids[city2]) 
              for city1 in direct_flights for city2 in direct_flights[city1]]
        ))
    
    # Constraint: Porto must be visited between day 16 and 18 (inclusive)
    porto_id = city_ids["Porto"]
    s.add(Or([days[i] == porto_id for i in range(15, 18)]))  # days are 0-based in code, 1-based in output
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        day_sequence = [model.evaluate(day).as_long() for day in days]
        
        # Process the day sequence to create the itinerary
        current_place = id_to_city[day_sequence[0]]
        start_day = 1
        for i in range(1, total_days):
            if day_sequence[i] != day_sequence[i-1]:
                # Add the stay before the flight
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_place})
                # Add the flight day (duplicate for departure and arrival)
                itinerary.append({"day_range": f"Day {i}", "place": current_place})
                new_place = id_to_city[day_sequence[i]]
                itinerary.append({"day_range": f"Day {i}", "place": new_place})
                current_place = new_place
                start_day = i + 1
            # else: continue the stay
        # Add the last stay
        if start_day <= total_days:
            if start_day == total_days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_scheduling_problem()
import json
print(json.dumps(result, indent=2))