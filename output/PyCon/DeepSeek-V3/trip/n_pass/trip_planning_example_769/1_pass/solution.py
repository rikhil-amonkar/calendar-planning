import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    problem = Problem()
    
    # Define cities and their required days
    cities = ["Porto", "Prague", "Reykjavik", "Santorini", "Amsterdam", "Munich"]
    required_days = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4
    }
    
    # Define direct flight connections
    direct_flights = [
        ("Porto", "Amsterdam"), ("Munich", "Amsterdam"), ("Reykjavik", "Amsterdam"),
        ("Munich", "Porto"), ("Prague", "Reykjavik"), ("Reykjavik", "Munich"),
        ("Amsterdam", "Santorini"), ("Prague", "Amsterdam"), ("Prague", "Munich")
    ]
    
    # Make flights bidirectional
    flight_connections = set()
    for city1, city2 in direct_flights:
        flight_connections.add((city1, city2))
        flight_connections.add((city2, city1))
    
    # Create variables for arrival day for each city
    for city in cities:
        problem.addVariable(f"arrival_{city}", range(1, 17))
    
    # Create variables for departure day for each city
    for city in cities:
        problem.addVariable(f"departure_{city}", range(1, 17))
    
    # Constraint: Departure must be after arrival
    for city in cities:
        problem.addConstraint(lambda a, d, rd=required_days[city]: d >= a + rd - 1, 
                            (f"arrival_{city}", f"departure_{city}"))
    
    # Constraint: Total days must be 16
    def total_days_constraint(*args):
        arrivals = args[:len(cities)]
        departures = args[len(cities):]
        days_used = 0
        last_departure = 0
        
        # Create timeline of stays
        events = []
        for i, city in enumerate(cities):
            arrival = arrivals[i]
            departure = departures[i]
            events.append((arrival, 'arrival', city))
            events.append((departure, 'departure', city))
        
        events.sort()
        
        current_cities = set()
        day_count = 0
        current_day = 1
        
        for event_day, event_type, city in events:
            if event_day > current_day:
                if current_cities:
                    day_count += (event_day - current_day)
                current_day = event_day
            
            if event_type == 'arrival':
                current_cities.add(city)
            else:
                current_cities.remove(city)
        
        return day_count == 16
    
    all_vars = [f"arrival_{city}" for city in cities] + [f"departure_{city}" for city in cities]
    problem.addConstraint(total_days_constraint, all_vars)
    
    # Constraint: No overlapping stays in different cities
    for i, city1 in enumerate(cities):
        for j, city2 in enumerate(cities):
            if i != j:
                problem.addConstraint(
                    lambda a1, d1, a2, d2: d1 < a2 or d2 < a1,
                    (f"arrival_{city1}", f"departure_{city1}", f"arrival_{city2}", f"departure_{city2}")
                )
    
    # Constraint: Flight connections between consecutive cities
    def flight_connection_constraint(*args):
        arrivals = args[:len(cities)]
        departures = args[len(cities):]
        
        # Create sequence of visits
        visits = [(arrivals[i], departures[i], cities[i]) for i in range(len(cities))]
        visits.sort()
        
        for i in range(len(visits) - 1):
            _, dep_city1, city1 = visits[i]
            arr_city2, _, city2 = visits[i + 1]
            
            # Check if there's a direct flight between consecutive cities
            if (city1, city2) not in flight_connections:
                return False
            
            # Departure from city1 should be same day as arrival in city2
            if dep_city1 != arr_city2:
                return False
        
        return True
    
    problem.addConstraint(flight_connection_constraint, all_vars)
    
    # Special constraints
    # Porto: 5 days
    problem.addConstraint(lambda a, d: d == a + 4, ("arrival_Porto", "departure_Porto"))
    
    # Prague: 4 days  
    problem.addConstraint(lambda a, d: d == a + 3, ("arrival_Prague", "departure_Prague"))
    
    # Reykjavik: 4 days, wedding between day 4-7
    problem.addConstraint(lambda a, d: d == a + 3, ("arrival_Reykjavik", "departure_Reykjavik"))
    problem.addConstraint(lambda a: a <= 4 and a + 3 >= 4, ("arrival_Reykjavik",))
    problem.addConstraint(lambda d: d >= 7, ("departure_Reykjavik",))
    
    # Santorini: 2 days
    problem.addConstraint(lambda a, d: d == a + 1, ("arrival_Santorini", "departure_Santorini"))
    
    # Amsterdam: 2 days, conference day 14-15
    problem.addConstraint(lambda a, d: d == a + 1, ("arrival_Amsterdam", "departure_Amsterdam"))
    problem.addConstraint(lambda a: a <= 14, ("arrival_Amsterdam",))
    problem.addConstraint(lambda d: d >= 15, ("departure_Amsterdam",))
    
    # Munich: 4 days, friend between day 7-10
    problem.addConstraint(lambda a, d: d == a + 3, ("arrival_Munich", "departure_Munich"))
    problem.addConstraint(lambda a: a <= 7, ("arrival_Munich",))
    problem.addConstraint(lambda d: d >= 10, ("departure_Munich",))
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first solution
    solution = solutions[0]
    
    # Create visit list
    visits = []
    for city in cities:
        arrival = solution[f"arrival_{city}"]
        departure = solution[f"departure_{city}"]
        visits.append((arrival, departure, city))
    
    # Sort by arrival day
    visits.sort()
    
    # Build itinerary
    itinerary = []
    for arrival, departure, city in visits:
        day_range = f"Day {arrival}-{departure}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))