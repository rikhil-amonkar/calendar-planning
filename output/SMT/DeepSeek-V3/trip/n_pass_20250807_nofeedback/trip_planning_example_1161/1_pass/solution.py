import json
from z3 import *

def solve_scheduling_problem():
    # Define the cities and their required days
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
    
    # Direct flights: adjacency list
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
    
    # Create flight adjacency matrix
    flight_adj = [[False for _ in range(len(city_list))] for _ in range(len(city_list))]
    for city in direct_flights:
        for dest in direct_flights[city]:
            i = city_to_int[city]
            j = city_to_int[dest]
            flight_adj[i][j] = True
            flight_adj[j][i] = True  # assuming flights are bidirectional
    
    # Initialize Z3 solver
    s = Solver()
    
    # Variables: day[i] is the city visited on day i+1 (days are 1-based)
    days = [Int(f"day_{i}") for i in range(18)]  # days 1..18
    
    # Each day must be a valid city index
    for d in days:
        s.add(And(d >= 0, d < len(city_list)))
    
    # Constraint: Mykonos between day 15 and 18 (inclusive)
    mykonos_idx = city_to_int["Mykonos"]
    s.add(Sum([If(days[i] == mykonos_idx, 1, 0) for i in range(14, 18)]) == 4)  # days 15-18
    
    # Constraint: Krakow 5 days
    krakow_idx = city_to_int["Krakow"]
    s.add(Sum([If(days[i] == krakow_idx, 1, 0) for i in range(18)]) == 5)
    
    # Constraint: Vilnius 2 days
    vilnius_idx = city_to_int["Vilnius"]
    s.add(Sum([If(days[i] == vilnius_idx, 1, 0) for i in range(18)]) == 2)
    
    # Constraint: Helsinki 2 days
    helsinki_idx = city_to_int["Helsinki"]
    s.add(Sum([If(days[i] == helsinki_idx, 1, 0) for i in range(18)]) == 2)
    
    # Constraint: Dubrovnik 3 days, including days 2-4 (indices 1-3 in 0-based)
    dubrovnik_idx = city_to_int["Dubrovnik"]
    s.add(Sum([If(days[i] == dubrovnik_idx, 1, 0) for i in range(18)]) == 3)
    s.add(And(days[1] == dubrovnik_idx, days[2] == dubrovnik_idx, days[3] == dubrovnik_idx))
    
    # Constraint: Oslo 2 days, including day 1 or 2 (indices 0 or 1)
    oslo_idx = city_to_int["Oslo"]
    s.add(Sum([If(days[i] == oslo_idx, 1, 0) for i in range(18)]) == 2)
    s.add(Or(days[0] == oslo_idx, days[1] == oslo_idx))
    
    # Constraint: Madrid 5 days
    madrid_idx = city_to_int["Madrid"]
    s.add(Sum([If(days[i] == madrid_idx, 1, 0) for i in range(18)]) == 5)
    
    # Constraint: Paris 2 days
    paris_idx = city_to_int["Paris"]
    s.add(Sum([If(days[i] == paris_idx, 1, 0) for i in range(18)]) == 2)
    
    # Flight constraints: consecutive days must be connected by a direct flight or same city
    for i in range(17):
        current_city = days[i]
        next_city = days[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            And([Implies(current_city == city_idx, Or([next_city == dest_idx for dest_idx in range(len(city_list)) if flight_adj[city_idx][dest_idx]])) for city_idx in range(len(city_list))])
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(18):
            city_idx = m.evaluate(days[i]).as_long()
            itinerary.append({"day": i+1, "place": int_to_city[city_idx]})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; the solver should have ensured this)
        city_days = {city: 0 for city in city_list}
        for entry in itinerary:
            city_days[entry["place"]] += 1
        
        assert city_days["Mykonos"] == 4
        assert city_days["Krakow"] == 5
        assert city_days["Vilnius"] == 2
        assert city_days["Helsinki"] == 2
        assert city_days["Dubrovnik"] == 3
        assert city_days["Oslo"] == 2
        assert city_days["Madrid"] == 5
        assert city_days["Paris"] == 2
        
        # Verify specific day constraints
        assert itinerary[1]["place"] == "Dubrovnik"  # day 2
        assert itinerary[2]["place"] == "Dubrovnik"  # day 3
        assert itinerary[3]["place"] == "Dubrovnik"  # day 4
        assert (itinerary[0]["place"] == "Oslo" or itinerary[1]["place"] == "Oslo")
        
        # Mykonos between day 15-18
        mykonos_days = [entry["day"] for entry in itinerary if entry["place"] == "Mykonos"]
        assert all(15 <= day <= 18 for day in mykonos_days)
        assert len(mykonos_days) == 4
        
        # Verify flight connections
        for i in range(17):
            current_place = itinerary[i]["place"]
            next_place = itinerary[i+1]["place"]
            if current_place != next_place:
                assert next_place in direct_flights[current_place]
        
        # Prepare the output
        output = {"itinerary": itinerary}
        return output
    else:
        raise Exception("No valid itinerary found")

# Generate the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))