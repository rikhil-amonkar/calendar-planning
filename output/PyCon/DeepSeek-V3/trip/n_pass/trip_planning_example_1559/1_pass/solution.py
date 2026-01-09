import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and their required days
    cities = {
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    
    # Define direct flight connections
    connections = {
        'Lisbon': ['Paris', 'Seville', 'Prague', 'Valencia', 'Nice', 'Oslo', 'Lyon'],
        'Paris': ['Lisbon', 'Oslo', 'Valencia', 'Nice', 'Lyon', 'Tallinn', 'Prague', 'Seville'],
        'Lyon': ['Nice', 'Prague', 'Paris', 'Valencia', 'Oslo'],
        'Nice': ['Lyon', 'Paris', 'Mykonos', 'Oslo', 'Lisbon'],
        'Oslo': ['Tallinn', 'Paris', 'Prague', 'Nice', 'Lyon', 'Lisbon'],
        'Seville': ['Lisbon', 'Paris', 'Valencia'],
        'Tallinn': ['Oslo', 'Paris', 'Prague'],
        'Mykonos': ['Nice'],
        'Prague': ['Lyon', 'Lisbon', 'Oslo', 'Paris', 'Valencia', 'Tallinn'],
        'Valencia': ['Paris', 'Lisbon', 'Lyon', 'Seville', 'Prague']
    }
    
    # Define special constraints
    special_constraints = [
        ('Valencia', 3, 4),  # Valencia between day 3-4
        ('Oslo', 13, 15),    # Oslo between day 13-15
        ('Seville', 5, 9),   # Seville between day 5-9
        ('Mykonos', 21, 25)  # Mykonos between day 21-25
    ]
    
    problem = Problem()
    
    # Create variables for start day of each city visit
    city_vars = {}
    for city in cities:
        city_vars[city] = f"start_{city}"
    
    # Add variables with domain (possible start days)
    total_days = 25
    for city, var_name in city_vars.items():
        max_start = total_days - cities[city] + 1
        problem.addVariable(var_name, range(1, max_start + 1))
    
    # Constraint: All cities must be visited exactly once with their required duration
    # This means no overlapping visits to different cities
    for i, city1 in enumerate(cities):
        for j, city2 in enumerate(cities):
            if i < j:
                var1 = city_vars[city1]
                var2 = city_vars[city2]
                dur1 = cities[city1]
                dur2 = cities[city2]
                
                # Either city1 ends before city2 starts OR city2 ends before city1 starts
                problem.addConstraint(
                    lambda s1, s2, d1=dur1, d2=dur2: (s1 + d1 <= s2) or (s2 + d2 <= s1),
                    (var1, var2)
                )
    
    # Constraint: Travel must be via direct flights between consecutive cities
    city_list = list(cities.keys())
    for i in range(len(city_list)):
        for j in range(len(city_list)):
            if i != j:
                city1 = city_list[i]
                city2 = city_list[j]
                var1 = city_vars[city1]
                var2 = city_vars[city2]
                dur1 = cities[city1]
                
                # If city2 starts immediately after city1 ends, they must be connected
                problem.addConstraint(
                    lambda s1, s2, c1=city1, c2=city2, d1=dur1: 
                    not (s1 + d1 == s2) or (c2 in connections.get(c1, [])),
                    (var1, var2)
                )
    
    # Special time window constraints
    for city, min_day, max_day in special_constraints:
        var_name = city_vars[city]
        dur = cities[city]
        
        # The visit must overlap with the specified time window
        problem.addConstraint(
            lambda start, d=dur, min_d=min_day, max_d=max_day: 
            start <= max_day and start + d - 1 >= min_day,
            (var_name,)
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create itinerary with day ranges
    itinerary = []
    for city in cities:
        start_day = solution[city_vars[city]]
        end_day = start_day + cities[city] - 1
        day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
    
    # Sort by start day
    itinerary.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()