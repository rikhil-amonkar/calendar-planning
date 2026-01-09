import json
from constraint import Problem, AllDifferentConstraint

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
        problem.addConstraint(lambda start, c=city: get_end_day(c, start) <= 19, [start_days[city]])
    
    # Constraint: No overlapping visits
    for i in range(len(cities)):
        for j in range(i + 1, len(cities)):
            city1, city2 = cities[i], cities[j]
            problem.addConstraint(
                lambda start1, start2, c1=city1, c2=city2: 
                get_end_day(c1, start1) < start2 or get_end_day(c2, start2) < start1,
                [start_days[city1], start_days[city2]]
            )
    
    # Revised specific constraints from the problem
    # Lisbon: 2 days, workshop between day 4 and 5
    # This means the 2-day visit must cover both day 4 and 5
    problem.addConstraint(lambda start: start <= 4 and get_end_day("Lisbon", start) >= 5, [start_days["Lisbon"]])
    
    # Tallinn: 2 days, meet friend between day 1 and 2
    # This means the 2-day visit must cover both day 1 and 2
    problem.addConstraint(lambda start: start == 1, [start_days["Tallinn"]])
    
    # Stockholm: 4 days, wedding between day 13 and 16
    # This means the 4-day visit must cover days 13-16
    problem.addConstraint(lambda start: start <= 13 and get_end_day("Stockholm", start) >= 16, [start_days["Stockholm"]])
    
    # Lyon: 2 days, annual show between day 18 and 19
    # This means the 2-day visit must cover both day 18 and 19
    problem.addConstraint(lambda start: start == 18, [start_days["Lyon"]])
    
    # Flight connectivity constraints - simplified approach
    # Instead of using positions, we'll use a simpler connectivity check
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
    
    # Create a simpler connectivity constraint
    # We'll ensure that for any two consecutive cities in the chronological order, there's a flight
    def check_connectivity(*starts):
        # Create list of (city, start_day) pairs
        city_starts = [(city, starts[i]) for i, city in enumerate(cities)]
        # Sort by start day to get visit order
        city_starts.sort(key=lambda x: x[1])
        
        # Check connectivity between consecutive cities in the visit order
        for i in range(len(city_starts) - 1):
            city1 = city_starts[i][0]
            city2 = city_starts[i + 1][0]
            if (city1, city2) not in all_flights:
                return False
        return True
    
    # Get all start day variables
    start_vars = [start_days[city] for city in cities]
    
    # Add connectivity constraint
    problem.addConstraint(check_connectivity, start_vars)
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create itinerary with city visits
    itinerary_data = []
    
    # Get city visits with start and end days
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