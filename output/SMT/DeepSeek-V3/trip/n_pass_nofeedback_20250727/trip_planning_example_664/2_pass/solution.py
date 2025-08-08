from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        "Milan": ["Stockholm", "Munich", "Seville"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Munich": ["Stockholm", "Bucharest", "Seville", "Milan", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }
    
    # Days: 1 to 18
    days = 18
    day_range = range(1, days + 1)
    
    # Create Z3 variables: for each day, which city (index)
    city_vars = [Int(f"day_{day}") for day in day_range]
    
    # Solver
    s = Solver()
    
    # Each day's variable must be a valid city index (0 to 5)
    for day in day_range:
        s.add(city_vars[day - 1] >= 0, city_vars[day - 1] < len(cities))
    
    # Duration constraints
    # Tallinn: 2 days
    s.add(Sum([If(city_vars[day - 1] == city_to_idx["Tallinn"], 1, 0) for day in day_range]) == 2)
    # Bucharest: 4 days (must be between day 1 and day 4)
    s.add(Sum([If(And(city_vars[day - 1] == city_to_idx["Bucharest"], day >= 1, day <= 4), 1, 0) for day in day_range]) == 4)
    # Seville: 5 days (must include at least one day between day 8 and day 12)
    s.add(Sum([If(city_vars[day - 1] == city_to_idx["Seville"], 1, 0) for day in day_range]) == 5)
    s.add(Sum([If(And(city_vars[day - 1] == city_to_idx["Seville"], day >= 8, day <= 12), 1, 0) for day in day_range]) >= 1)
    # Stockholm: 5 days
    s.add(Sum([If(city_vars[day - 1] == city_to_idx["Stockholm"], 1, 0) for day in day_range]) == 5)
    # Munich: 5 days (must be between day 4 and day 8)
    s.add(Sum([If(And(city_vars[day - 1] == city_to_idx["Munich"], day >= 4, day <= 8), 1, 0) for day in day_range]) == 5)
    # Milan: 2 days
    s.add(Sum([If(city_vars[day - 1] == city_to_idx["Milan"], 1, 0) for day in day_range]) == 2)
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for day in range(1, days):
        current_city_var = city_vars[day - 1]
        next_city_var = city_vars[day]
        same_city = current_city_var == next_city_var
        flight_possible = False
        for city in direct_flights:
            for adj in direct_flights[city]:
                flight_possible = Or(flight_possible, And(current_city_var == city_to_idx[city], next_city_var == city_to_idx[adj]))
        s.add(Or(same_city, flight_possible))
    
    # Additional constraints to ensure the time windows are respected
    # Bucharest must be the first city (day 1)
    s.add(city_vars[0] == city_to_idx["Bucharest"])
    # Munich must start by day 4
    s.add(Or([city_vars[day - 1] == city_to_idx["Munich"] for day in range(4, 9)]))
    # Seville must have at least one day between day 8 and day 12
    s.add(Or([city_vars[day - 1] == city_to_idx["Seville"] for day in range(8, 13)]))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in day_range:
            city_idx = model.evaluate(city_vars[day - 1]).as_long()
            itinerary.append({"day": day, "place": cities[city_idx]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)