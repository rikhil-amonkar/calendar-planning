from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Reykjavik", "Stuttgart", "Oslo", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn", "Oslo"],
        "Stockholm": ["Oslo", "Stuttgart", "Split", "Geneva", "Reykjavik"],
        "Stuttgart": ["Porto", "Reykjavik", "Stockholm", "Split"],
        "Oslo": ["Stockholm", "Split", "Geneva", "Porto", "Tallinn", "Reykjavik"],
        "Split": ["Stuttgart", "Oslo", "Stockholm", "Geneva"],
        "Geneva": ["Porto", "Oslo", "Stockholm", "Split"],
        "Porto": ["Stuttgart", "Oslo", "Geneva"],
        "Tallinn": ["Oslo", "Reykjavik"]
    }
    
    # Create a Z3 solver
    s = Solver()
    
    # Variables: for each day (1..21), which city is visited
    day_city = [Int(f"day_{day}_city") for day in range(1, 22)]
    
    # Constraint: each day's city must be one of the 8 cities (0..7)
    for day in range(21):
        s.add(And(day_city[day] >= 0, day_city[day] < 8))
    
    # Fixed events:
    # Days 1-2: Reykjavik (index 0)
    s.add(day_city[0] == city_to_idx["Reykjavik"])
    s.add(day_city[1] == city_to_idx["Reykjavik"])
    
    # Workshop in Porto between day 19-21 (indices 18-20)
    s.add(day_city[18] == city_to_idx["Porto"])
    s.add(day_city[19] == city_to_idx["Porto"])
    s.add(day_city[20] == city_to_idx["Porto"])
    
    # Meet friend in Stockholm between day 2-4 (indices 1-3)
    # At least one of days 2,3,4 is Stockholm (indices 1,2,3)
    s.add(Or(day_city[1] == city_to_idx["Stockholm"], 
             day_city[2] == city_to_idx["Stockholm"], 
             day_city[3] == city_to_idx["Stockholm"]))
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for day in range(20):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # Either same city or connected
        same_city = current_city == next_city
        # Or there's a direct flight
        flight_possible = False
        for city1 in direct_flights:
            idx1 = city_to_idx[city1]
            for city2 in direct_flights[city1]:
                idx2 = city_to_idx[city2]
                flight_possible = Or(flight_possible, And(current_city == idx1, next_city == idx2))
                flight_possible = Or(flight_possible, And(current_city == idx2, next_city == idx1))
        s.add(Or(same_city, flight_possible))
    
    # Duration constraints:
    # Oslo: 5 days
    oslo_days = Sum([If(day_city[day] == city_to_idx["Oslo"], 1, 0) for day in range(21)])
    s.add(oslo_days == 5)
    
    # Stuttgart: 5 days
    stuttgart_days = Sum([If(day_city[day] == city_to_idx["Stuttgart"], 1, 0) for day in range(21)])
    s.add(stuttgart_days == 5)
    
    # Reykjavik: 2 days (already fixed days 1-2)
    reykjavik_days = Sum([If(day_city[day] == city_to_idx["Reykjavik"], 1, 0) for day in range(21)])
    s.add(reykjavik_days == 2)
    
    # Split: 3 days
    split_days = Sum([If(day_city[day] == city_to_idx["Split"], 1, 0) for day in range(21)])
    s.add(split_days == 3)
    
    # Geneva: 2 days
    geneva_days = Sum([If(day_city[day] == city_to_idx["Geneva"], 1, 0) for day in range(21)])
    s.add(geneva_days == 2)
    
    # Porto: 3 days (days 19-21 are already 3 days)
    porto_days = Sum([If(day_city[day] == city_to_idx["Porto"], 1, 0) for day in range(21)])
    s.add(porto_days == 3)
    
    # Tallinn: 5 days
    tallinn_days = Sum([If(day_city[day] == city_to_idx["Tallinn"], 1, 0) for day in range(21)])
    s.add(tallinn_days == 5)
    
    # Stockholm: 3 days
    stockholm_days = Sum([If(day_city[day] == city_to_idx["Stockholm"], 1, 0) for day in range(21)])
    s.add(stockholm_days == 3)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(21):
            city_idx = m.evaluate(day_city[day]).as_long()
            city = cities[city_idx]
            itinerary.append({"day": day + 1, "city": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
result = solve_itinerary()
print(result)