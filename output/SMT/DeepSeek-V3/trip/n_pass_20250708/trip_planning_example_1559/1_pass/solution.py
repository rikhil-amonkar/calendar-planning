from z3 import *
import json

def solve_itinerary():
    # Cities to visit with their required days
    cities = {
        "Valencia": 2,
        "Oslo": 3,
        "Lyon": 4,
        "Prague": 3,
        "Paris": 4,
        "Nice": 4,
        "Seville": 5,
        "Tallinn": 2,
        "Mykonos": 5,
        "Lisbon": 2
    }
    
    # Direct flights
    direct_flights = {
        "Lisbon": ["Paris", "Seville", "Prague", "Valencia", "Nice", "Oslo", "Lyon"],
        "Paris": ["Lisbon", "Oslo", "Nice", "Lyon", "Tallinn", "Prague", "Seville", "Valencia"],
        "Lyon": ["Nice", "Prague", "Paris", "Valencia", "Oslo", "Lisbon"],
        "Nice": ["Lyon", "Paris", "Oslo", "Mykonos", "Lisbon"],
        "Tallinn": ["Oslo", "Prague", "Paris"],
        "Prague": ["Lyon", "Lisbon", "Oslo", "Paris", "Tallinn", "Valencia"],
        "Oslo": ["Tallinn", "Paris", "Prague", "Nice", "Lyon", "Lisbon"],
        "Seville": ["Lisbon", "Paris", "Valencia"],
        "Valencia": ["Paris", "Lisbon", "Lyon", "Prague", "Seville"],
        "Mykonos": ["Nice"]
    }
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Create variables for each day (1..25), each variable represents a city
    days = [Int(f"day_{i}") for i in range(1, 26)]
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraint: each day variable must be one of the city IDs
    for day in days:
        solver.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraint: total days per city must match requirements
    for city, total_days in cities.items():
        solver.add(Sum([If(day == city_ids[city], 1, 0) for day in days]) == total_days)
    
    # Event constraints
    # Valencia between day 3 and day 4 (inclusive)
    solver.add(Or(days[2] == city_ids["Valencia"], days[3] == city_ids["Valencia"]))
    
    # Oslo between day 13 and day 15 (inclusive)
    solver.add(Or([days[i] == city_ids["Oslo"] for i in range(12, 15)]))
    
    # Seville's show between day 5 and day 9 (inclusive)
    for i in range(4, 9):
        solver.add(days[i] == city_ids["Seville"])
    
    # Mykonos wedding between day 21 and day 25 (inclusive)
    wedding_days = [days[i] == city_ids["Mykonos"] for i in range(20, 25)]
    solver.add(Or(wedding_days))
    # Ensure at least 5 days in Mykonos, but the wedding is within 21-25
    # (handled by total days constraint)
    
    # Flight constraints: consecutive days must be either same city or connected by direct flight
    for i in range(24):
        current_day = days[i]
        next_day = days[i+1]
        solver.add(Or(
            current_day == next_day,
            *[And(current_day == city_ids[city1], next_day == city_ids[city2]) 
              for city1 in cities for city2 in direct_flights.get(city1, [])]
        ))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        # Helper to add entries to itinerary
        def add_entry(start, end, place):
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": place})
            else:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": place})
        
        # Generate the itinerary from the model
        for day in range(1, 26):
            city_id = model.evaluate(days[day-1]).as_long()
            city = id_to_city[city_id]
            if day == 1:
                current_place = city
                start_day = 1
            else:
                prev_city_id = model.evaluate(days[day-2]).as_long()
                prev_city = id_to_city[prev_city_id]
                if city != prev_city:
                    # Flight day: add previous city's stay, then flight entries for both
                    add_entry(start_day, day-1, prev_city)
                    itinerary.append({"day_range": f"Day {day-1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day-1}", "place": city})
                    current_place = city
                    start_day = day
                else:
                    continue
        
        # Add the last stay
        add_entry(start_day, 25, current_place)
        
        # Post-process to merge consecutive days in the same city (if any separated by flights)
        # But according to the problem's note, flight days should have separate entries.
        # So the above should suffice.
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))