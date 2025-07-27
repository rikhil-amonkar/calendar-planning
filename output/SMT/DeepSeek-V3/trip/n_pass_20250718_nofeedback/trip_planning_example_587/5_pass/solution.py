from z3 import *

def solve_scheduling():
    # Cities
    cities = ['Manchester', 'Istanbul', 'Venice', 'Krakow', 'Lyon']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Manchester': ['Venice', 'Istanbul', 'Krakow'],
        'Istanbul': ['Manchester', 'Venice', 'Krakow', 'Lyon'],
        'Venice': ['Manchester', 'Istanbul', 'Lyon'],
        'Krakow': ['Istanbul', 'Manchester'],
        'Lyon': ['Venice', 'Istanbul']
    }
    
    # Required days in each city
    required_days = {
        'Manchester': 3,
        'Istanbul': 7,
        'Venice': 7,
        'Krakow': 6,
        'Lyon': 2
    }
    
    total_days = 21
    
    # Create a Z3 solver with a timeout
    solver = Solver()
    solver.set("timeout", 60000)  # 60 seconds timeout
    
    # Variables: for each day, which city are we in?
    day_city = [Int(f"day_{d}_city") for d in range(total_days)]
    
    # Constraints: each day_city must be between 0 and 4 (indices of cities)
    for d in range(total_days):
        solver.add(day_city[d] >= 0, day_city[d] < len(cities))
    
    # Constraints on transitions: consecutive days must be either same city or connected by direct flight
    for d in range(total_days - 1):
        current_city = day_city[d]
        next_city = day_city[d + 1]
        # Either same city or a direct flight
        same_city = current_city == next_city
        direct_flight_options = []
        for city in cities:
            for neighbor in direct_flights[city]:
                direct_flight_options.append(And(current_city == city_to_idx[city], next_city == city_to_idx[neighbor]))
        solver.add(Or(same_city, Or(direct_flight_options)))
    
    # Required days per city: count occurrences of each city index in day_city
    for city in cities:
        count = Sum([If(day_city[d] == city_to_idx[city], 1, 0) for d in range(total_days)])
        solver.add(count == required_days[city])
    
    # Manchester must be visited on at least one of days 1-3 (indices 0-2)
    solver.add(Or([day_city[d] == city_to_idx['Manchester'] for d in range(3)]))
    
    # Workshop in Venice between day 3 and day 9 (indices 2-8)
    solver.add(Sum([If(And(day_city[d] == city_to_idx['Venice'], d >= 2, d <= 8), 1, 0) for d in range(total_days)]) >= 1)
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for d in range(total_days):
            city_idx = model.evaluate(day_city[d]).as_long()
            city = cities[city_idx]
            itinerary.append({"day": d + 1, "place": city})
        
        # Format the output as required
        output = {
            "itinerary": itinerary
        }
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver
result = solve_scheduling()
print(result)