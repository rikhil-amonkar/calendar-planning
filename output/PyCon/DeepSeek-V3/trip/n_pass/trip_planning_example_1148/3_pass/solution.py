import json
from constraint import Problem

def solve_trip_plan():
    problem = Problem()
    
    cities = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
    
    # Define variables for start days of each city visit
    start_days = {}
    for city in cities:
        start_days[city] = f"{city}_start"
    
    # Add variables for start days (1 to 19)
    for city in cities:
        problem.addVariable(start_days[city], range(1, 20))
    
    # Define durations for each city
    durations = {
        "Lisbon": 2,
        "Dubrovnik": 5,
        "Copenhagen": 5,
        "Prague": 3,
        "Tallinn": 2,
        "Stockholm": 4,
        "Split": 3,
        "Lyon": 2
    }
    
    # Calculate end days
    def get_end_day(city, start):
        return start + durations[city] - 1
    
    # Constraint: All visits must be within the 19-day trip
    for city in cities:
        problem.addConstraint(lambda start, city=city: get_end_day(city, start) <= 19, [start_days[city]])
    
    # Constraint: No overlapping visits
    for i in range(len(cities)):
        for j in range(i + 1, len(cities)):
            city1, city2 = cities[i], cities[j]
            problem.addConstraint(
                lambda start1, start2, city1=city1, city2=city2: 
                get_end_day(city1, start1) < start2 or get_end_day(city2, start2) < start1,
                [start_days[city1], start_days[city2]]
            )
    
    # Specific constraints from the problem
    # Lisbon: 2 days, workshop between day 4 and 5
    problem.addConstraint(lambda start: start <= 4 and get_end_day("Lisbon", start) >= 5, [start_days["Lisbon"]])
    
    # Tallinn: 2 days, meet friend between day 1 and 2
    problem.addConstraint(lambda start: start <= 1 and get_end_day("Tallinn", start) >= 2, [start_days["Tallinn"]])
    
    # Stockholm: 4 days, wedding between day 13 and 16
    problem.addConstraint(lambda start: start <= 13 and get_end_day("Stockholm", start) >= 16, [start_days["Stockholm"]])
    
    # Lyon: 2 days, annual show between day 18 and 19
    problem.addConstraint(lambda start: start <= 18 and get_end_day("Lyon", start) >= 19, [start_days["Lyon"]])
    
    # Flight connectivity constraints
    direct_flights = [
        ("Dubrovnik", "Stockholm"), ("Lisbon", "Copenhagen"), ("Lisbon", "Lyon"),
        ("Copenhagen", "Stockholm"), ("Copenhagen", "Split"), ("Prague", "Stockholm"),
        ("Tallinn", "Stockholm"), ("Prague", "Lyon"), ("Lisbon", "Stockholm"),
        ("Prague", "Lisbon"), ("Stockholm", "Split"), ("Prague", "Copenhagen"),
        ("Split", "Lyon"), ("Copenhagen", "Dubrovnik"), ("Prague", "Split"),
        ("Tallinn", "Copenhagen"), ("Tallinn", "Prague")
    ]
    
    # Create bidirectional flights
    all_flights = direct_flights + [(b, a) for (a, b) in direct_flights]
    
    # Create a variable for the order of cities (as indices)
    # This represents the sequence in which cities are visited
    problem.addVariable("visit_order", range(len(cities)))
    
    # We need to create variables for each position in the sequence
    position_vars = [f"pos_{i}" for i in range(len(cities))]
    for var in position_vars:
        problem.addVariable(var, range(len(cities)))
    
    # Constraint: All positions must be unique (permutation)
    problem.addConstraint(AllDifferentConstraint(), position_vars)
    
    # Constraint: Consecutive cities in the itinerary must have direct flights
    def valid_flight_connectivity(*positions):
        # positions is a list of city indices in visit order
        for i in range(len(positions) - 1):
            city1 = cities[positions[i]]
            city2 = cities[positions[i + 1]]
            if (city1, city2) not in all_flights:
                return False
        return True
    
    problem.addConstraint(valid_flight_connectivity, position_vars)
    
    # Constraint: The start days must be consistent with the visit order
    def days_match_order(*args):
        # args contains positions followed by start days
        positions = args[:len(cities)]
        starts = args[len(cities):]
        
        # Create mapping from city index to start day
        city_starts = {}
        for i, pos in enumerate(positions):
            city_starts[pos] = starts[i]
        
        # Check if starts are in increasing order according to visit order
        for i in range(len(positions) - 1):
            city1_idx = positions[i]
            city2_idx = positions[i + 1]
            city1 = cities[city1_idx]
            city2 = cities[city2_idx]
            
            start1 = city_starts[city1_idx]
            start2 = city_starts[city2_idx]
            end1 = get_end_day(city1, start1)
            
            # City2 must start after city1 ends (at least 1 day gap for travel)
            if start2 <= end1:
                return False
        return True
    
    # Get all start day variables
    start_vars = [start_days[city] for city in cities]
    
    # Add constraint connecting positions and start days
    problem.addConstraint(days_match_order, position_vars + start_vars)
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create itinerary with city visits
    itinerary_data = []
    
    # Get the visit order from the solution
    positions = [solution[var] for var in position_vars]
    
    # Sort cities by their start day to get chronological order
    city_visits = []
    for city in cities:
        start = solution[start_days[city]]
        end = get_end_day(city, start)
        city_visits.append((city, start, end))
    
    # Sort by start day
    city_visits.sort(key=lambda x: x[1])
    
    # Create the itinerary in the required format
    for city, start, end in city_visits:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary_data.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary_data}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))