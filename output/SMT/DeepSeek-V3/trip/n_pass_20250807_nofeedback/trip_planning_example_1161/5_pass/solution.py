import json
from z3 import *

def solve_scheduling_problem():
    # Define cities and required days
    cities = {
        "Mykonos": 4,
        "Krakow": 5,
        "Vilnius": 2,
        "Helsinki": 2,
        "Dubrovnik": 3,
        "Oslo": 2,
        "Madrid": 5,
        "Paris": 2
    }
    
    city_list = list(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_list)}
    int_to_city = {idx: city for idx, city in enumerate(city_list)}
    
    # Corrected flight connections (bidirectional)
    direct_flights = {
        "Oslo": ["Krakow", "Paris", "Madrid", "Helsinki", "Dubrovnik", "Vilnius"],
        "Paris": ["Oslo", "Madrid", "Krakow", "Helsinki", "Vilnius"],
        "Madrid": ["Paris", "Oslo", "Dubrovnik", "Helsinki", "Mykonos"],
        "Helsinki": ["Vilnius", "Oslo", "Krakow", "Dubrovnik", "Paris", "Madrid"],
        "Dubrovnik": ["Helsinki", "Madrid", "Oslo"],
        "Krakow": ["Oslo", "Paris", "Helsinki", "Vilnius"],
        "Vilnius": ["Helsinki", "Oslo", "Paris", "Krakow"],
        "Mykonos": ["Madrid"]
    }
    
    # Initialize solver
    s = Solver()
    
    # Day variables (1-18)
    days = [Int(f"day_{i}") for i in range(18)]
    for d in days:
        s.add(And(d >= 0, d < len(city_list)))
    
    # Mykonos: any 4 days between 15-18 (more flexible)
    mykonos_idx = city_to_int["Mykonos"]
    s.add(Sum([If(days[i] == mykonos_idx, 1, 0) for i in range(14, 18)]) == 4)
    
    # Other city duration constraints
    for city, days_req in cities.items():
        if city != "Mykonos":
            idx = city_to_int[city]
            s.add(Sum([If(days[i] == idx, 1, 0) for i in range(18)]) == days_req)
    
    # Specific day constraints
    dubrovnik_idx = city_to_int["Dubrovnik"]
    s.add(And(days[1] == dubrovnik_idx, days[2] == dubrovnik_idx, days[3] == dubrovnik_idx))
    
    oslo_idx = city_to_int["Oslo"]
    s.add(Or(days[0] == oslo_idx, days[1] == oslo_idx))
    
    # Flight constraints
    for i in range(17):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            Or([And(current == city_idx, next_day == dest_idx) 
               for city_idx in range(len(city_list)) 
               for dest_idx in range(len(city_list)) 
               if int_to_city[city_idx] in direct_flights and 
                  int_to_city[dest_idx] in direct_flights[int_to_city[city_idx]]])
        ))
    
    # Try to find solution
    if s.check() == sat:
        m = s.model()
        itinerary = [{"day": i+1, "place": int_to_city[m.evaluate(days[i]).as_long()]} for i in range(18)]
        
        # Verification
        city_counts = {city: 0 for city in cities}
        for day in itinerary:
            city_counts[day["place"]] += 1
        
        for city, req in cities.items():
            assert city_counts[city] == req, f"{city} day count mismatch"
        
        # Mykonos days verification
        mykonos_days = [d["day"] for d in itinerary if d["place"] == "Mykonos"]
        assert all(15 <= day <= 18 for day in mykonos_days), "Mykonos days out of range"
        assert len(mykonos_days) == 4, "Wrong Mykonos day count"
        
        # Dubrovnik days verification
        assert itinerary[1]["place"] == "Dubrovnik", "Day 2 not Dubrovnik"
        assert itinerary[2]["place"] == "Dubrovnik", "Day 3 not Dubrovnik"
        assert itinerary[3]["place"] == "Dubrovnik", "Day 4 not Dubrovnik"
        
        # Oslo days verification
        assert itinerary[0]["place"] == "Oslo" or itinerary[1]["place"] == "Oslo", "Oslo not on day 1 or 2"
        
        # Flight connections verification
        for i in range(17):
            current = itinerary[i]["place"]
            next_p = itinerary[i+1]["place"]
            if current != next_p:
                assert next_p in direct_flights[current], f"No flight from {current} to {next_p}"
        
        return {"itinerary": itinerary}
    else:
        raise Exception("No valid itinerary found with current constraints")

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))