from z3 import *

def solve_scheduling_problem():
    # Cities
    cities = ["Oslo", "Krakow", "Vilnius", "Helsinki", "Dubrovnik", "Madrid", "Mykonos", "Paris"]
    city_vars = {city: city for city in cities}  # For readability
    
    # Direct flights (undirected)
    direct_flights = [
        ("Oslo", "Krakow"),
        ("Oslo", "Paris"),
        ("Paris", "Madrid"),
        ("Helsinki", "Vilnius"),
        ("Oslo", "Madrid"),
        ("Oslo", "Helsinki"),
        ("Helsinki", "Krakow"),
        ("Dubrovnik", "Helsinki"),
        ("Dubrovnik", "Madrid"),
        ("Oslo", "Dubrovnik"),
        ("Krakow", "Paris"),
        ("Madrid", "Mykonos"),
        ("Oslo", "Vilnius"),
        ("Krakow", "Vilnius"),
        ("Helsinki", "Paris"),
        ("Vilnius", "Paris"),
        ("Helsinki", "Madrid")
    ]
    
    # Create a set of direct flight pairs for easy lookup
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables for each day (1..18)
    days = [Int(f"day_{i}") for i in range(1, 19)]
    
    # Each day variable must be assigned a city (represented as an integer)
    city_ints = {city: idx for idx, city in enumerate(cities)}
    int_cities = {idx: city for idx, city in enumerate(cities)}
    
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Duration constraints
    # Mykonos: 4 days between day 15-18
    mykonos_days = [If(days[i] == city_ints["Mykonos"], 1, 0) for i in range(14, 18)]  # days 15-18 are indices 14-17
    s.add(sum(mykonos_days) == 4)
    
    # Krakow: 5 days total
    krakow_days = [If(days[i] == city_ints["Krakow"], 1, 0) for i in range(18)]
    s.add(sum(krakow_days) == 5)
    
    # Vilnius: 2 days
    vilnius_days = [If(days[i] == city_ints["Vilnius"], 1, 0) for i in range(18)]
    s.add(sum(vilnius_days) == 2)
    
    # Helsinki: 2 days
    helsinki_days = [If(days[i] == city_ints["Helsinki"], 1, 0) for i in range(18)]
    s.add(sum(helsinki_days) == 2)
    
    # Dubrovnik: 3 days, with days 2-4 (indices 1-3) including the show
    dubrovnik_days = [If(days[i] == city_ints["Dubrovnik"], 1, 0) for i in range(18)]
    s.add(sum(dubrovnik_days) == 3)
    # The show is from day 2-4, so likely all three days are Dubrovnik
    s.add(And([days[i] == city_ints["Dubrovnik"] for i in range(1, 4)]))  # days 2-4 are Dubrovnik
    
    # Oslo: 2 days, meet friends between day 1-2 (indices 0-1)
    oslo_days = [If(days[i] == city_ints["Oslo"], 1, 0) for i in range(18)]
    s.add(sum(oslo_days) == 2)
    s.add(Or(days[0] == city_ints["Oslo"], days[1] == city_ints["Oslo"]))
    
    # Madrid: 5 days
    madrid_days = [If(days[i] == city_ints["Madrid"], 1, 0) for i in range(18)]
    s.add(sum(madrid_days) == 5)
    
    # Paris: 2 days
    paris_days = [If(days[i] == city_ints["Paris"], 1, 0) for i in range(18)]
    s.add(sum(paris_days) == 2)
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(17):
        current_city = days[i]
        next_city = days[i+1]
        # Either same city or a direct flight exists
        same_city = current_city == next_city
        flight_exists = Or([And(current_city == city_ints[a], next_city == city_ints[b]) for a, b in flight_pairs])
        s.add(Or(same_city, flight_exists))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(18):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = int_cities[city_idx]
            itinerary.append({"day": day_num, "place": city})
        
        # Output as JSON-formatted dictionary
        result = {"itinerary": itinerary}
        return result
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
import json
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))