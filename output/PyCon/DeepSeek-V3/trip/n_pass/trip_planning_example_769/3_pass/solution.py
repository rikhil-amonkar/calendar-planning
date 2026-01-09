import json
from constraint import Problem

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
    
    # Define direct flight connections (bidirectional)
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
    
    # Create variables for arrival day for each city (1-16)
    for city in cities:
        problem.addVariable(f"arrival_{city}", range(1, 17))
    
    # Create variables for departure day for each city
    for city in cities:
        problem.addVariable(f"departure_{city}", range(1, 17))
    
    # Constraint: Stay duration matches required days
    for city in cities:
        problem.addConstraint(
            lambda a, d, rd=required_days[city]: d == a + rd - 1,
            (f"arrival_{city}", f"departure_{city}")
        )
    
    # Constraint: All cities have different arrival days (visit each city exactly once)
    arrival_vars = [f"arrival_{city}" for city in cities]
    problem.addConstraint(lambda *args: len(set(args)) == len(args), arrival_vars)
    
    # Constraint: Total trip duration is exactly 16 days
    def total_days_constraint(*args):
        # Args contains all arrival and departure variables in order
        arrivals = args[:len(cities)]
        departures = args[len(cities):]
        
        earliest_arrival = min(arrivals)
        latest_departure = max(departures)
        return latest_departure - earliest_arrival + 1 == 16
    
    # Add total days constraint with all variables
    all_vars = arrival_vars + [f"departure_{city}" for city in cities]
    problem.addConstraint(total_days_constraint, all_vars)
    
    # Constraint: Sequential travel with flight connections
    def travel_sequence_constraint(*args):
        # Args contains all arrival and departure variables
        arrivals = args[:len(cities)]
        departures = args[len(cities):]
        
        # Create list of (arrival, departure, city)
        visits = []
        for i, city in enumerate(cities):
            visits.append((arrivals[i], departures[i], city))
        
        # Sort by arrival day
        visits.sort()
        
        # Check consecutive cities have flight connections and proper sequencing
        for i in range(len(visits) - 1):
            arr1, dep1, city1 = visits[i]
            arr2, dep2, city2 = visits[i + 1]
            
            # Next city must start the day after previous city ends
            if arr2 != dep1 + 1:
                return False
            
            # Check flight connection exists
            if (city1, city2) not in flight_connections:
                return False
        
        return True
    
    problem.addConstraint(travel_sequence_constraint, all_vars)
    
    # Special constraints
    # Reykjavik: wedding between day 4-7 (must be in Reykjavik during days 4-7)
    problem.addConstraint(lambda a: a <= 4, ("arrival_Reykjavik",))
    problem.addConstraint(lambda d: d >= 7, ("departure_Reykjavik",))
    
    # Amsterdam: conference day 14-15 (must be in Amsterdam during days 14-15)
    problem.addConstraint(lambda a: a <= 14, ("arrival_Amsterdam",))
    problem.addConstraint(lambda d: d >= 15, ("departure_Amsterdam",))
    
    # Munich: friend between day 7-10 (must be in Munich during days 7-10)
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