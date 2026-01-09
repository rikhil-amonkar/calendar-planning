import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and their required days
    cities = {
        'Valencia': 5,
        'Riga': 5,
        'Prague': 3,
        'Mykonos': 3,
        'Zurich': 5,
        'Bucharest': 5,
        'Nice': 2
    }
    
    total_days = 22
    
    # Define direct flight connections
    direct_flights = [
        ('Mykonos', 'Nice'), ('Mykonos', 'Zurich'),
        ('Prague', 'Bucharest'), ('Valencia', 'Bucharest'),
        ('Zurich', 'Prague'), ('Riga', 'Nice'),
        ('Zurich', 'Riga'), ('Zurich', 'Bucharest'),
        ('Zurich', 'Valencia'), ('Bucharest', 'Riga'),
        ('Prague', 'Riga'), ('Prague', 'Valencia'),
        ('Zurich', 'Nice')
    ]
    
    # Make flights bidirectional
    bidirectional_flights = set()
    for city1, city2 in direct_flights:
        bidirectional_flights.add((city1, city2))
        bidirectional_flights.add((city2, city1))
    
    # Define special constraints
    prague_constraint = (7, 9)  # Prague between day 7 and 9
    mykonos_constraint = (1, 3)  # Mykonos between day 1 and 3
    
    problem = Problem()
    
    # Create variables for start day of each city visit
    city_vars = {}
    for city in cities:
        city_vars[city] = f"{city}_start"
    
    # Define possible start days (1 to total_days)
    for city, var_name in city_vars.items():
        problem.addVariable(var_name, range(1, total_days + 1))
    
    # Constraint: All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), list(city_vars.values()))
    
    # Constraint: Cities must fit within total days
    for city, days_needed in cities.items():
        var_name = city_vars[city]
        problem.addConstraint(lambda start: start + days_needed - 1 <= total_days, [var_name])
    
    # Constraint: No overlapping visits
    for city1, days1 in cities.items():
        for city2, days2 in cities.items():
            if city1 != city2:
                start1 = city_vars[city1]
                start2 = city_vars[city2]
                problem.addConstraint(
                    lambda s1, s2, d1=days1, d2=days2: 
                    s1 + d1 <= s2 or s2 + d2 <= s1,
                    [start1, start2]
                )
    
    # Constraint: Special date constraints
    prague_start = city_vars['Prague']
    problem.addConstraint(lambda start: prague_constraint[0] <= start <= prague_constraint[1] - cities['Prague'] + 1, [prague_start])
    
    mykonos_start = city_vars['Mykonos']
    problem.addConstraint(lambda start: mykonos_constraint[0] <= start <= mykonos_constraint[1] - cities['Mykonos'] + 1, [mykonos_start])
    
    # Constraint: Flight connectivity - consecutive cities must have direct flights
    def get_city_order(solution):
        # Sort cities by start day
        ordered_cities = sorted([(start, city) for city, start in solution.items()])
        return [city for _, city in ordered_cities]
    
    def check_flight_connectivity(solution):
        ordered_cities = get_city_order(solution)
        
        # Check consecutive pairs have direct flights
        for i in range(len(ordered_cities) - 1):
            city1 = ordered_cities[i]
            city2 = ordered_cities[i + 1]
            
            if (city1, city2) not in bidirectional_flights:
                return False
        
        return True
    
    problem.addConstraint(check_flight_connectivity, list(city_vars.values()))
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Extract start days for each city
    city_starts = {}
    for city, var_name in city_vars.items():
        city_starts[city] = solution[var_name]
    
    # Create itinerary with day ranges
    itinerary = []
    for start_day, city in sorted([(start, city) for city, start in city_starts.items()]):
        end_day = start_day + cities[city] - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()