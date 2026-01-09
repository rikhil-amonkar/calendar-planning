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
    
    # Constraint: No overlapping stays
    def no_overlap_constraint(*args):
        # Args contains all arrival and departure variables
        arrivals = args[:len(cities)]
        departures = args[len(cities):]
        
        # Check each pair of cities for overlap
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                arr_i, dep_i = arrivals[i], departures[i]
                arr_j, dep_j = arrivals[j], departures[j]
                
                # If the stays overlap, return False
                if not (dep_i < arr_j or dep_j < arr_i):
                    return False
        return True
    
    all_vars = arrival_vars + [f"departure_{city}" for city in cities]
    problem.addConstraint(no_overlap_constraint, all_vars)
    
    # Constraint: Total trip duration is exactly 16 days
    def total_days_constraint(*args):
        arrivals = args[:len(cities)]
        departures = args[len(cities):]
        
        earliest_arrival = min(arrivals)
        latest_departure = max(departures)
        return latest_departure - earliest_arrival + 1 == 16
    
    problem.addConstraint(total_days_constraint, all_vars)
    
    # Constraint: Travel sequence with flight connections
    def travel_sequence_constraint(*args):
        arrivals = args[:len(cities)]
        departures = args[len(cities):]
        
        # Create list of (arrival, departure, city)
        visits = []
        for i, city in enumerate(cities):
            visits.append((arrivals[i], departures[i], city))
        
        # Sort by arrival day
        visits.sort()
        
        # Check consecutive cities in the itinerary have flight connections
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
    
    # Special constraints (relaxed to be more flexible)
    # Reykjavik: wedding between day 4-7 (must be in Reykjavik during days 4-7)
    problem.addConstraint(lambda a, d: a <= 4 and d >= 7, 
                         ("arrival_Reykjavik", "departure_Reykjavik"))
    
    # Amsterdam: conference day 14-15 (must be in Amsterdam during days 14-15)
    problem.addConstraint(lambda a, d: a <= 14 and d >= 15, 
                         ("arrival_Amsterdam", "departure_Amsterdam"))
    
    # Munich: friend between day 7-10 (must be in Munich during days 7-10)
    problem.addConstraint(lambda a, d: a <= 7 and d >= 10, 
                         ("arrival_Munich", "departure_Munich"))
    
    # Solve the problem with a time limit
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try a more relaxed approach if no solution found
        return find_alternative_solution()
    
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

def find_alternative_solution():
    """Alternative approach with more flexible constraints"""
    problem = Problem()
    
    cities = ["Porto", "Prague", "Reykjavik", "Santorini", "Amsterdam", "Munich"]
    required_days = {
        "Porto": 5, "Prague": 4, "Reykjavik": 4, 
        "Santorini": 2, "Amsterdam": 2, "Munich": 4
    }
    
    # Flight connections (simplified - focus on reachability)
    connections = {
        "Porto": ["Amsterdam", "Munich"],
        "Prague": ["Reykjavik", "Amsterdam", "Munich"],
        "Reykjavik": ["Prague", "Amsterdam", "Munich"],
        "Santorini": ["Amsterdam"],
        "Amsterdam": ["Porto", "Munich", "Reykjavik", "Santorini", "Prague"],
        "Munich": ["Porto", "Amsterdam", "Reykjavik", "Prague"]
    }
    
    # Create position variables (1-6) for each city
    for city in cities:
        problem.addVariable(f"pos_{city}", range(1, 7))
    
    # All cities have different positions
    problem.addConstraint(lambda *args: len(set(args)) == len(args), 
                         [f"pos_{city}" for city in cities])
    
    # Convert positions to arrival days
    def build_itinerary_from_positions(solution):
        # Get positions
        positions = []
        for city in cities:
            positions.append((solution[f"pos_{city}"], city))
        
        # Sort by position
        positions.sort()
        
        # Build itinerary with proper day assignments
        current_day = 1
        itinerary = []
        
        for pos, city in positions:
            stay_days = required_days[city]
            arrival = current_day
            departure = arrival + stay_days - 1
            
            # Check if this fits within 16 days
            if departure > 16:
                return None
            
            itinerary.append((arrival, departure, city))
            current_day = departure + 1
        
        # Check if we used exactly 16 days
        if current_day - 1 != 16:
            return None
        
        # Check flight connections
        for i in range(len(itinerary) - 1):
            city1 = itinerary[i][2]
            city2 = itinerary[i + 1][2]
            if city2 not in connections[city1]:
                return None
        
        # Check special constraints
        reykjavik_visit = next((visit for visit in itinerary if visit[2] == "Reykjavik"), None)
        amsterdam_visit = next((visit for visit in itinerary if visit[2] == "Amsterdam"), None)
        munich_visit = next((visit for visit in itinerary if visit[2] == "Munich"), None)
        
        if reykjavik_visit and not (reykjavik_visit[0] <= 4 and reykjavik_visit[1] >= 7):
            return None
        if amsterdam_visit and not (amsterdam_visit[0] <= 14 and amsterdam_visit[1] >= 15):
            return None
        if munich_visit and not (munich_visit[0] <= 7 and munich_visit[1] >= 10):
            return None
        
        return itinerary
    
    # Try to find a valid sequence
    solutions = problem.getSolutions()
    
    for solution in solutions:
        itinerary = build_itinerary_from_positions(solution)
        if itinerary:
            result = []
            for arrival, departure, city in itinerary:
                result.append({"day_range": f"Day {arrival}-{departure}", "place": city})
            return {"itinerary": result}
    
    return {"error": "No valid itinerary found"}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))