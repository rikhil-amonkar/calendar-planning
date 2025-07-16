from z3 import *

def solve_itinerary():
    # Define the cities
    cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Days are from 1 to 15
    days = list(range(1, 16))
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Create variables: for each day, the city visited
    city_vars = [Int(f"day_{day}") for day in days]
    
    # Each city_var must be between 0 and 6 (index of cities)
    for var in city_vars:
        s.add(var >= 0, var < len(cities))
    
    # Flight connections: list of tuples (from, to) city indices
    flight_connections = [
        (city_indices["London"], city_indices["Amsterdam"]),
        (city_indices["Vilnius"], city_indices["Frankfurt"]),
        (city_indices["Riga"], city_indices["Vilnius"]),
        (city_indices["Riga"], city_indices["Stockholm"]),
        (city_indices["London"], city_indices["Bucharest"]),
        (city_indices["Amsterdam"], city_indices["Stockholm"]),
        (city_indices["Amsterdam"], city_indices["Frankfurt"]),
        (city_indices["Frankfurt"], city_indices["Stockholm"]),
        (city_indices["Bucharest"], city_indices["Riga"]),
        (city_indices["Amsterdam"], city_indices["Riga"]),
        (city_indices["Amsterdam"], city_indices["Bucharest"]),
        (city_indices["Riga"], city_indices["Frankfurt"]),
        (city_indices["Bucharest"], city_indices["Frankfurt"]),
        (city_indices["London"], city_indices["Frankfurt"]),
        (city_indices["London"], city_indices["Stockholm"]),
        (city_indices["Amsterdam"], city_indices["Vilnius"])
    ]
    
    # Ensure that consecutive day transitions are either same city or connected by flights
    for i in range(len(days) - 1):
        current_day_var = city_vars[i]
        next_day_var = city_vars[i + 1]
        # Either stay in the same city or move to a connected city
        same_city = (current_day_var == next_day_var)
        flight_possible = Or([And(current_day_var == fr, next_day_var == to) for fr, to in flight_connections] +
                            [And(current_day_var == to, next_day_var == fr) for fr, to in flight_connections])
        s.add(Or(same_city, flight_possible))
    
    # Duration constraints
    # Riga: 2 days
    s.add(Sum([If(city_vars[i] == city_indices["Riga"], 1, 0) for i in range(len(days))]) == 2)
    # Frankfurt: 3 days
    s.add(Sum([If(city_vars[i] == city_indices["Frankfurt"], 1, 0) for i in range(len(days))]) == 3)
    # Amsterdam: 2 days
    s.add(Sum([If(city_vars[i] == city_indices["Amsterdam"], 1, 0) for i in range(len(days))]) == 2)
    # Vilnius: 5 days
    s.add(Sum([If(city_vars[i] == city_indices["Vilnius"], 1, 0) for i in range(len(days))]) == 5)
    # London: 2 days
    s.add(Sum([If(city_vars[i] == city_indices["London"], 1, 0) for i in range(len(days))]) == 2)
    # Stockholm: 3 days
    s.add(Sum([If(city_vars[i] == city_indices["Stockholm"], 1, 0) for i in range(len(days))]) == 3)
    # Bucharest: 4 days
    s.add(Sum([If(city_vars[i] == city_indices["Bucharest"], 1, 0) for i in range(len(days))]) == 4)
    
    # Event constraints
    # Meet friend in Amsterdam between day 2 and day 3: So Amsterdam must include day 2 or day 3 or both.
    s.add(Or(
        city_vars[1] == city_indices["Amsterdam"],  # day 2 is index 1 (0-based)
        city_vars[2] == city_indices["Amsterdam"]   # day 3 is index 2
    ))
    
    # Workshop in Vilnius between day 7 and day 11: Vilnius must be visited on at least one day between 7 and 11 inclusive.
    s.add(Or([city_vars[i] == city_indices["Vilnius"] for i in range(6, 11)]))  # days 7-11 are indices 6 to 10
    
    # Wedding in Stockholm between day 13 and day 15: Stockholm must be visited on at least one day between 13 and 15 inclusive.
    s.add(Or([city_vars[i] == city_indices["Stockholm"] for i in range(12, 15)]))  # days 13-15 are indices 12 to 14
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        # Extract the city for each day
        day_assignments = [model.evaluate(city_vars[i]).as_long() for i in range(len(days))]
        # Create the itinerary
        itinerary = []
        current_city = day_assignments[0]
        start_day = 1
        for i in range(1, len(days)):
            if day_assignments[i] != current_city:
                # Add the stay before the flight
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": cities[current_city]})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": cities[current_city]})
                # Add the flight day (current city and next city)
                itinerary.append({"day_range": f"Day {i}", "place": cities[current_city]})
                itinerary.append({"day_range": f"Day {i}", "place": cities[day_assignments[i]]})
                current_city = day_assignments[i]
                start_day = i + 1
            else:
                continue
        # Add the last stay
        if start_day == len(days):
            itinerary.append({"day_range": f"Day {start_day}", "place": cities[current_city]})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{len(days)}", "place": cities[current_city]})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))