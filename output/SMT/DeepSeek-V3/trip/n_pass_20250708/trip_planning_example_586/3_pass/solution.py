from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = ["Frankfurt", "Naples", "Helsinki", "Lyon", "Prague"]
    required_days = {
        "Frankfurt": 3,
        "Naples": 4,
        "Helsinki": 4,
        "Lyon": 3,
        "Prague": 2
    }
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections
    connections = [
        ("Prague", "Lyon"),
        ("Prague", "Frankfurt"),
        ("Frankfurt", "Lyon"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Prague", "Helsinki")
    ]
    # Create adjacency list
    adj = {i: [] for i in range(len(cities))}
    for a, b in connections:
        i = city_to_idx[a]
        j = city_to_idx[b]
        adj[i].append(j)
        adj[j].append(i)
    
    # Days are 1..12
    days_total = 12
    
    # Variables:
    # For each day d, city_in[d] is the primary city (0..4), and is_flight[d] is a boolean.
    # If is_flight[d], then next_city[d] is the city flown to (must be adjacent to city_in[d]).
    city_in = [Int(f"city_in_{d}") for d in range(days_total)]
    is_flight = [Bool(f"is_flight_{d}") for d in range(days_total)]
    next_city = [Int(f"next_city_{d}") for d in range(days_total)]
    
    s = Solver()
    
    for d in range(days_total):
        s.add(city_in[d] >= 0, city_in[d] < len(cities))
        s.add(Implies(is_flight[d], And(next_city[d] >= 0, next_city[d] < len(cities))))
        # Ensure flight is only to connected cities
        for c in range(len(cities)):
            s.add(Implies(And(is_flight[d], city_in[d] == c), Or([next_city[d] == j for j in adj[c]])))
        s.add(Implies(Not(is_flight[d]), next_city[d] == -1))
    
    # The city_in for day d+1 must be next_city[d] if is_flight[d], else city_in[d].
    for d in range(days_total - 1):
        s.add(city_in[d+1] == If(is_flight[d], next_city[d], city_in[d]))
    
    # Count the days spent in each city.
    city_days = [0]*len(cities)
    for c in range(len(cities)):
        for d in range(days_total):
            # The city c is visited on day d if city_in[d] == c or (is_flight[d] and next_city[d] == c)
            in_city = Or(city_in[d] == c, And(is_flight[d], next_city[d] == c))
            city_days[c] += If(in_city, 1, 0)
    
    # Add required days constraints.
    for city, days in required_days.items():
        s.add(city_days[city_to_idx[city]] == days)
    
    # Helsinki show from day 2 to 5 (1-based: days 1..4 in 0-based).
    for d in [1, 2, 3, 4]:
        s.add(Or(city_in[d] == city_to_idx["Helsinki"], 
                 And(is_flight[d], next_city[d] == city_to_idx["Helsinki"])))
    
    # Workshop in Prague between day 1 and 2 (0-based days 0 and 1).
    s.add(Or(
        Or(city_in[0] == city_to_idx["Prague"], And(is_flight[0], next_city[0] == city_to_idx["Prague"])),
        Or(city_in[1] == city_to_idx["Prague"], And(is_flight[1], next_city[1] == city_to_idx["Prague"]))
    ))
    
    # Check for model.
    if s.check() == sat:
        m = s.model()
        
        itinerary = []
        
        current_city = None
        start_day = 0
        
        for d in range(days_total):
            primary = m.evaluate(city_in[d]).as_long()
            primary_name = cities[primary]
            is_flight_d = is_true(m.evaluate(is_flight[d]))
            
            if is_flight_d:
                next_c = m.evaluate(next_city[d]).as_long()
                next_name = cities[next_c]
                
                # Add the current stay up to day d.
                if current_city is not None:
                    if start_day == d:
                        day_str = f"Day {d+1}"
                    else:
                        day_str = f"Day {start_day+1}-{d+1}"
                    itinerary.append({"day_range": day_str, "place": current_city})
                
                # Add flight day entries.
                itinerary.append({"day_range": f"Day {d+1}", "place": primary_name})
                itinerary.append({"day_range": f"Day {d+1}", "place": next_name})
                
                current_city = next_name
                start_day = d
            else:
                if current_city is None:
                    current_city = primary_name
                    start_day = d
                elif current_city == primary_name:
                    pass  # continue the stay.
                else:
                    # End previous stay.
                    if start_day == d-1:
                        day_str = f"Day {start_day+1}"
                    else:
                        day_str = f"Day {start_day+1}-{d}"
                    itinerary.append({"day_range": day_str, "place": current_city})
                    current_city = primary_name
                    start_day = d
        
        # Add the last stay.
        if current_city is not None:
            if start_day == days_total - 1:
                day_str = f"Day {start_day+1}"
            else:
                day_str = f"Day {start_day+1}-{days_total}"
            itinerary.append({"day_range": day_str, "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found."}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))