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
        # Count days in city (including flight days)
        in_city = [If(day == cid, 1, 0) for day in days]
        # For flight days, we'll subtract the double-counted days later
        s.add(Sum(in_city) >= cities[city])
    
    # Constraint: Reykjavik between day 10-12 (wedding)
    s.add(Or(days[9] == city_ids["Reykjavik"], 
            days[10] == city_ids["Reykjavik"], 
            days[11] == city_ids["Reykjavik"]))
    
    # Constraint: Vilnius between day 7-9 (visiting relatives)
    s.add(Or(days[6] == city_ids["Vilnius"], 
            days[7] == city_ids["Vilnius"], 
            days[8] == city_ids["Vilnius"]))
    
    # Constraint: flights are only direct (including reverse flights)
    flight_pairs = []
    for city1, city2 in direct_flights:
        flight_pairs.append((city_ids[city1], city_ids[city2]))
        flight_pairs.append((city_ids[city2], city_ids[city1]))
    
    for i in range(11):  # days 1..12, transitions between i and i+1 (0-based)
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or take a direct flight
        s.add(Or(current == next_day, 
                Or([And(current == c1, next_day == c2) for c1, c2 in flight_pairs])))
    
    # Additional constraint: ensure we don't exceed total days when accounting for flights
    # Each flight day counts as 1 day (not double-counted in total)
    s.add(Sum([If(day == city_ids[city], 1, 0) for city in city_ids for day in days]) == 12 + 11)
    
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
        
        # Verify day counts meet requirements
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            if '-' in entry['day_range']:
                start, end = map(int, entry['day_range'].replace('Day ', '').split('-'))
                day_counts[entry['place']] += end - start + 1
            else:
                day_counts[entry['place']] += 1
        
        # Adjust for flight days (remove double-counting)
        for i in range(1, len(itinerary)):
            if itinerary[i]['day_range'] == itinerary[i-1]['day_range']:
                day_counts[itinerary[i]['place']] -= 1
        
        # Final verification
        valid = True
        for city, req in cities.items():
            if day_counts[city] != req:
                valid = False
                break
        
        if valid:
            return {"itinerary": itinerary}
        else:
            return {"error": "Found itinerary doesn't meet requirements"}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))