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
    
    # Constraint: Consecutive cities in the itinerary must have direct flights
    # We'll use a different approach - create an ordering constraint
    def has_flight_between(city1, city2):
        return (city1, city2) in all_flights
    
    # Create a variable for the order of cities
    # We'll represent the order as a permutation of cities
    problem.addVariable("city_order", [tuple(cities)])
    
    # Constraint for flight connectivity between consecutive cities
    def valid_flight_connectivity(order):
        order_list = order[0]  # Extract the tuple from the list
        for i in range(len(order_list) - 1):
            if not has_flight_between(order_list[i], order_list[i+1]):
                return False
        return True
    
    problem.addConstraint(valid_flight_connectivity, ["city_order"])
    
    # Constraint: The start days must match the order
    def days_match_order(order, *starts):
        order_list = order[0]
        city_starts = list(zip(order_list, starts))
        # Check if starts are in increasing order
        for i in range(len(city_starts) - 1):
            city1, start1 = city_starts[i]
            city2, start2 = city_starts[i + 1]
            end1 = get_end_day(city1, start1)
            # Allow at least 1 day for travel between cities
            if start2 <= end1:
                return False
        return True
    
    # Get all start day variables in city order
    start_vars = [start_days[city] for city in cities]
    problem.addConstraint(days_match_order, ["city_order"] + start_vars)
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create itinerary with city visits
    itinerary_data = []
    city_visits = []
    
    # Get the actual order from the solution
    actual_order = solution["city_order"][0]
    
    for city in actual_order:
        start = solution[start_days[city]]
        end = get_end_day(city, start)
        city_visits.append((city, start, end))
    
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