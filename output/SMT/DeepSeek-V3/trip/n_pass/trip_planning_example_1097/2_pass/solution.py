from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3
    }
    
    # Direct flights as a set of tuples
    direct_flights = {
        ("Warsaw", "Reykjavik"),
        ("Oslo", "Madrid"),
        ("Warsaw", "Riga"),
        ("Lyon", "London"),
        ("Madrid", "London"),
        ("Warsaw", "London"),
        ("Reykjavik", "Madrid"),
        ("Warsaw", "Oslo"),
        ("Oslo", "Dubrovnik"),
        ("Oslo", "Reykjavik"),
        ("Riga", "Oslo"),
        ("Oslo", "Lyon"),
        ("Oslo", "London"),
        ("London", "Reykjavik"),
        ("Warsaw", "Madrid"),
        ("Madrid", "Lyon"),
        ("Dubrovnik", "Madrid")
    }
    
    # Make flights bidirectional
    bidirectional_flights = set()
    for (a, b) in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights
    
    # Total days
    total_days = 18
    
    # Create Z3 variables: itinerary[d] is the city on day d (1-based)
    itinerary = [Int(f"day_{d}") for d in range(1, total_days + 1)]
    
    # City to integer mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Solver
    s = Solver()
    
    # Each day must be one of the cities
    for day in itinerary:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraint: consecutive days must have a direct flight or stay in the same city
    for i in range(len(itinerary) - 1):
        current_city = itinerary[i]
        next_city = itinerary[i + 1]
        # Either same city or there's a direct flight
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == city_ids[a], next_city == city_ids[b]) for (a, b) in direct_flights])
        ))
    
    # Constraints for total days in each city
    for city, days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(itinerary[d] == city_id, 1, 0) for d in range(total_days)]) == days)
    
    # Specific constraints:
    # 1. Meet friend in Riga between day 4 and 5: so Riga must include day 4 or 5.
    s.add(Or(itinerary[3] == city_ids["Riga"], itinerary[4] == city_ids["Riga"]))
    
    # 2. Wedding in Dubrovnik between day 7 and 8: so Dubrovnik must include day 7 or 8.
    s.add(Or(itinerary[6] == city_ids["Dubrovnik"], itinerary[7] == city_ids["Dubrovnik"]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary_result = []
        for d in range(total_days):
            city_id = m.evaluate(itinerary[d]).as_long()
            city = id_to_city[city_id]
            itinerary_result.append({"day": d + 1, "place": city})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should ensure it)
        return {"itinerary": itinerary_result}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))