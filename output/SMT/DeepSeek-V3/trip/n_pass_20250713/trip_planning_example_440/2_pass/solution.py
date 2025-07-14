from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6
    }
    
    # Direct flight connections (bidirectional)
    direct_flights = [
        ("Split", "Helsinki"),
        ("Geneva", "Split"),
        ("Geneva", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Vilnius", "Helsinki"),
        ("Split", "Vilnius")
    ]
    
    # Add reverse flights
    all_flights = set()
    for flight in direct_flights:
        all_flights.add(flight)
        all_flights.add((flight[1], flight[0]))
    
    # Create Z3 solver
    s = Solver()
    
    # Variables: day_i represents the city on day i (1-based)
    days = [Int(f"day_{i}") for i in range(1, 13)]
    
    # City encodings
    city_ids = {
        "Split": 0,
        "Helsinki": 1,
        "Reykjavik": 2,
        "Vilnius": 3,
        "Geneva": 4
    }
    id_to_city = {v: k for k, v in city_ids.items()}
    
    # Constraint: each day is assigned a valid city
    for day in days:
        s.add(day >= 0, day <= 4)
    
    # Constraint: total days per city
    for city, cid in city_ids.items():
        total = Sum([If(day == cid, 1, 0) for day in days])
        s.add(total == cities[city])
    
    # Constraint: Reykjavik between day 10-12 (wedding)
    s.add(Or([days[i] == city_ids["Reykjavik"] for i in range(9, 12)]))
    
    # Constraint: Vilnius between day 7-9 (visiting relatives)
    s.add(Or([days[i] == city_ids["Vilnius"] for i in range(6, 9)]))
    
    # Constraint: flights are only direct
    for i in range(11):  # days 1..12, transitions between i and i+1 (0-based)
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or take a direct flight
        s.add(Or(
            current_day == next_day,
            Or([And(current_day == city_ids[city1], next_day == city_ids[city2]) 
                for (city1, city2) in all_flights])
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary_days = []
        for i in range(12):
            day_num = i + 1
            city_id = m.evaluate(days[i]).as_long()
            city = id_to_city[city_id]
            itinerary_days.append((day_num, city))
        
        # Process to create day ranges and handle flights
        itinerary = []
        current_place = itinerary_days[0][1]
        start_day = 1
        
        for i in range(1, 12):
            day_num, place = itinerary_days[i]
            if place != current_place:
                # Add the stay up to previous day
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_place})
                # Add the flight day for departure and arrival
                itinerary.append({"day_range": f"Day {i}", "place": current_place})
                itinerary.append({"day_range": f"Day {i}", "place": place})
                current_place = place
                start_day = i + 1
        
        # Add the last stay
        if start_day <= 12:
            if start_day == 12:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-12", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))