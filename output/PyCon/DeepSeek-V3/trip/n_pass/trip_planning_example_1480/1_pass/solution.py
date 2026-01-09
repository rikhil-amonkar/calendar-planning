from constraint import Problem
import json

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = {
        'Istanbul': 4,
        'Vienna': 4,
        'Riga': 2,
        'Brussels': 2,
        'Madrid': 4,
        'Vilnius': 4,
        'Venice': 5,
        'Geneva': 4,
        'Munich': 5,
        'Reykjavik': 2
    }
    
    # Direct flights between cities
    direct_flights = [
        ('Munich', 'Vienna'),
        ('Istanbul', 'Brussels'),
        ('Vienna', 'Vilnius'),
        ('Madrid', 'Munich'),
        ('Venice', 'Brussels'),
        ('Riga', 'Brussels'),
        ('Geneva', 'Istanbul'),
        ('Munich', 'Reykjavik'),
        ('Vienna', 'Istanbul'),
        ('Riga', 'Istanbul'),
        ('Reykjavik', 'Vienna'),
        ('Venice', 'Munich'),
        ('Madrid', 'Venice'),
        ('Vilnius', 'Istanbul'),
        ('Venice', 'Vienna'),
        ('Venice', 'Istanbul'),
        ('Reykjavik', 'Madrid'),
        ('Riga', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Reykjavik', 'Brussels'),
        ('Vilnius', 'Brussels'),
        ('Vilnius', 'Munich'),
        ('Madrid', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Geneva', 'Vienna'),
        ('Madrid', 'Brussels'),
        ('Vienna', 'Brussels'),
        ('Geneva', 'Brussels'),
        ('Geneva', 'Madrid'),
        ('Munich', 'Brussels'),
        ('Madrid', 'Istanbul'),
        ('Geneva', 'Munich'),
        ('Riga', 'Vilnius')
    ]
    
    # Create bidirectional flights
    all_flights = set()
    for city1, city2 in direct_flights:
        all_flights.add((city1, city2))
        all_flights.add((city2, city1))
    
    # Total days
    total_days = 27
    
    # Special constraints
    special_constraints = {
        'Brussels': {'start': 26, 'end': 27},  # Wedding in Brussels between day 26-27
        'Vilnius': {'start': 20, 'end': 23},   # Meet friends in Vilnius between day 20-23
        'Venice': {'start': 7, 'end': 11},     # Workshop in Venice between day 7-11
        'Geneva': {'start': 1, 'end': 4}       # Visit relatives in Geneva between day 1-4
    }
    
    # Variables: for each city, we need to track start day and end day
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, total_days + 1))
        problem.addVariable(f"{city}_end", range(1, total_days + 1))
    
    # Constraint 1: End day must be after start day
    for city, days in cities.items():
        problem.addConstraint(
            lambda start, end, d=days: end == start + d - 1,
            (f"{city}_start", f"{city}_end")
        )
    
    # Constraint 2: All visits must be within the 27-day period
    for city in cities:
        problem.addConstraint(
            lambda start: start >= 1 and start <= total_days,
            (f"{city}_start",)
        )
        problem.addConstraint(
            lambda end: end >= 1 and end <= total_days,
            (f"{city}_end",)
        )
    
    # Constraint 3: Special time constraints
    for city, constraint in special_constraints.items():
        problem.addConstraint(
            lambda start, end, c=constraint: start <= c['end'] and end >= c['start'],
            (f"{city}_start", f"{city}_end")
        )
    
    # Constraint 4: Cities cannot overlap in time (except for travel days)
    city_list = list(cities.keys())
    for i in range(len(city_list)):
        for j in range(i + 1, len(city_list)):
            city1 = city_list[i]
            city2 = city_list[j]
            problem.addConstraint(
                lambda s1, e1, s2, e2: (e1 < s2) or (e2 < s1),
                (f"{city1}_start", f"{city1}_end", f"{city2}_start", f"{city2}_end")
            )
    
    # Constraint 5: Travel constraints - consecutive cities must have direct flights
    # We'll model this by ensuring the itinerary order respects flight connections
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with strict constraints, relax some constraints
        print('{"itinerary": [], "error": "No valid itinerary found with given constraints"}')
        return
    
    # Take the first solution
    solution = solutions[0]
    
    # Create itinerary from solution
    itinerary = []
    for city in cities:
        start = solution[f"{city}_start"]
        end = solution[f"{city}_end"]
        itinerary.append({
            'city': city,
            'start': start,
            'end': end,
            'duration': end - start + 1
        })
    
    # Sort itinerary by start day
    itinerary.sort(key=lambda x: x['start'])
    
    # Format output as required
    output_itinerary = []
    for visit in itinerary:
        if visit['start'] == visit['end']:
            day_range = f"Day {visit['start']}"
        else:
            day_range = f"Day {visit['start']}-{visit['end']}"
        output_itinerary.append({
            'day_range': day_range,
            'place': visit['city']
        })
    
    # Output as JSON
    result = {'itinerary': output_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()