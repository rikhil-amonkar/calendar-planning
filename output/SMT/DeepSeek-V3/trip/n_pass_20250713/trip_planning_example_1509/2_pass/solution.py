import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Paris": 5,
        "Warsaw": 2,
        "Krakow": 2,
        "Tallinn": 2,
        "Riga": 2,
        "Copenhagen": 5,
        "Helsinki": 5,
        "Oslo": 5,
        "Santorini": 2,
        "Lyon": 4
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Warsaw", "Riga"),
        ("Warsaw", "Tallinn"),
        ("Copenhagen", "Helsinki"),
        ("Lyon", "Paris"),
        ("Copenhagen", "Warsaw"),
        ("Lyon", "Oslo"),
        ("Paris", "Oslo"),
        ("Paris", "Riga"),
        ("Krakow", "Helsinki"),
        ("Paris", "Tallinn"),
        ("Oslo", "Riga"),
        ("Krakow", "Warsaw"),
        ("Paris", "Helsinki"),
        ("Copenhagen", "Santorini"),
        ("Helsinki", "Warsaw"),
        ("Helsinki", "Riga"),
        ("Copenhagen", "Krakow"),
        ("Copenhagen", "Riga"),
        ("Paris", "Krakow"),
        ("Copenhagen", "Oslo"),
        ("Oslo", "Tallinn"),
        ("Oslo", "Helsinki"),
        ("Copenhagen", "Tallinn"),
        ("Oslo", "Krakow"),
        ("Riga", "Tallinn"),
        ("Helsinki", "Tallinn"),
        ("Paris", "Copenhagen"),
        ("Paris", "Warsaw"),
        ("Santorini", "Oslo"),
        ("Oslo", "Warsaw")
    ]
    
    # Add both directions for each flight
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    direct_flights = list(flight_pairs)
    
    # Create a dictionary for faster lookup
    flight_dict = {city: set() for city in cities}
    for a, b in direct_flights:
        flight_dict[a].add(b)
        flight_dict[b].add(a)
    
    # Days are 1..25
    days = 25
    
    # Create Z3 variables: assign each day to a city
    assignments = [Int(f"day_{i}") for i in range(1, days + 1)]
    
    # Create a mapping from city names to integers
    city_names = sorted(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_names)}
    int_to_city = {idx: city for idx, city in enumerate(city_names)}
    
    s = Solver()
    
    # Each day's assignment must be a valid city index
    for day in assignments:
        s.add(day >= 0, day < len(city_names))
    
    # Constraints for total days in each city
    for city, req_days in cities.items():
        city_idx = city_to_int[city]
        s.add(Sum([If(day == city_idx, 1, 0) for day in assignments]) == req_days)
    
    # Event constraints:
    # Paris: meet friends between day 4 and 8 (so at least one of days 4,5,6,7,8 must be in Paris)
    paris_idx = city_to_int["Paris"]
    s.add(Or([assignments[i] == paris_idx for i in range(3, 8)]))  # days 4-8 (0-based: 3..7)
    
    # Krakow: workshop between day 17-18 (so day 17 or 18 must be in Krakow)
    krakow_idx = city_to_int["Krakow"]
    s.add(Or(assignments[16] == krakow_idx, assignments[17] == krakow_idx))  # days 17-18
    
    # Riga: wedding between day 23-24 (so day 23 or 24 must be in Riga)
    riga_idx = city_to_int["Riga"]
    s.add(Or(assignments[22] == riga_idx, assignments[23] == riga_idx))  # days 23-24
    
    # Helsinki: meet friend between day 18-22 (so at least one of days 18-22 must be in Helsinki)
    helsinki_idx = city_to_int["Helsinki"]
    s.add(Or([assignments[i] == helsinki_idx for i in range(17, 22)]))  # days 18-22
    
    # Santorini: visit relatives between day 12-13 (so day 12 or 13 must be in Santorini)
    santorini_idx = city_to_int["Santorini"]
    s.add(Or(assignments[11] == santorini_idx, assignments[12] == santorini_idx))  # days 12-13
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(days - 1):
        current_city = assignments[i]
        next_city = assignments[i + 1]
        # Either same city or connected by a direct flight
        s.add(Or(
            current_city == next_city,
            And(current_city != next_city,
                Or([And(current_city == city_to_int[a], next_city == city_to_int[b]) for a, b in direct_flights]))
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Get the assigned cities for each day
        day_assignments = []
        for i in range(days):
            city_idx = m.evaluate(assignments[i]).as_long()
            day_assignments.append(int_to_city[city_idx])
        
        # Process the day assignments to generate the itinerary with flight days
        current_place = day_assignments[0]
        start_day = 1
        for i in range(1, days):
            if day_assignments[i] != current_place:
                # Flight day: day i+1 is the transition
                end_day = i
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                # Add the flight day entries for both cities
                itinerary.append({"day_range": f"Day {i}", "place": current_place})
                itinerary.append({"day_range": f"Day {i}", "place": day_assignments[i]})
                current_place = day_assignments[i]
                start_day = i + 1
        # Add the last stay
        if start_day <= days:
            end_day = days
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))