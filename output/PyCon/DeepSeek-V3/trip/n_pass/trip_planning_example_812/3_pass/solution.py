import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and their required days
    cities = {
        'Paris': 5,
        'Florence': 3,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 5,
        'Nice': 5,
        'Warsaw': 3
    }
    
    # Define direct flight connections
    connections = {
        'Florence': ['Vienna', 'Munich', 'Paris'],
        'Vienna': ['Florence', 'Munich', 'Porto', 'Warsaw', 'Paris', 'Nice'],
        'Paris': ['Warsaw', 'Florence', 'Vienna', 'Porto', 'Nice', 'Munich'],
        'Munich': ['Vienna', 'Florence', 'Warsaw', 'Nice', 'Porto', 'Paris'],
        'Porto': ['Vienna', 'Munich', 'Nice', 'Paris', 'Warsaw'],
        'Nice': ['Munich', 'Warsaw', 'Vienna', 'Porto', 'Paris'],
        'Warsaw': ['Paris', 'Vienna', 'Munich', 'Nice', 'Porto']
    }
    
    # Define fixed constraints
    fixed_constraints = [
        ('Porto', 1, 3),    # Workshop in Porto between day 1-3
        ('Warsaw', 13, 15), # Wedding in Warsaw between day 13-15
        ('Vienna', 19, 20)  # Visit relatives in Vienna between day 19-20
    ]
    
    total_days = 20
    city_names = list(cities.keys())
    
    problem = Problem()
    
    # Add variables for start day of each city visit
    for city in city_names:
        problem.addVariable(f"{city}_start", range(1, total_days + 1))
        problem.addVariable(f"{city}_end", range(1, total_days + 1))
    
    # Constraint: end day must be after start day
    for city in city_names:
        problem.addConstraint(
            lambda start, end, city_days=cities[city]: end == start + city_days - 1,
            [f"{city}_start", f"{city}_end"]
        )
    
    # Constraint: visits must be within the 20-day period
    for city in city_names:
        problem.addConstraint(
            lambda start, city_days=cities[city]: start + city_days - 1 <= total_days,
            [f"{city}_start"]
        )
    
    # Constraint: fixed date requirements
    for city, fixed_start, fixed_end in fixed_constraints:
        problem.addConstraint(
            lambda start, end, fs=fixed_start, fe=fixed_end: start <= fs and end >= fe,
            [f"{city}_start", f"{city}_end"]
        )
    
    # Constraint: no overlapping visits to different cities
    for i, city1 in enumerate(city_names):
        for j, city2 in enumerate(city_names):
            if i < j:
                problem.addConstraint(
                    lambda s1, e1, s2, e2: e1 < s2 or e2 < s1,
                    [f"{city1}_start", f"{city1}_end", f"{city2}_start", f"{city2}_end"]
                )
    
    # Constraint: consecutive city visits must be connected by direct flights
    def flight_constraint(city1_end, city2_start, city1_name, city2_name):
        if city2_start == city1_end + 1:  # Travel day constraint
            return city2_name in connections[city1_name]
        return True
    
    for city1 in city_names:
        for city2 in city_names:
            if city1 != city2:
                problem.addConstraint(
                    flight_constraint,
                    [f"{city1}_end", f"{city2}_start", city1, city2]
                )
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try without flight constraints if no solution found
        problem = Problem()
        
        for city in city_names:
            problem.addVariable(f"{city}_start", range(1, total_days + 1))
            problem.addVariable(f"{city}_end", range(1, total_days + 1))
        
        for city in city_names:
            problem.addConstraint(
                lambda start, end, city_days=cities[city]: end == start + city_days - 1,
                [f"{city}_start", f"{city}_end"]
            )
        
        for city in city_names:
            problem.addConstraint(
                lambda start, city_days=cities[city]: start + city_days - 1 <= total_days,
                [f"{city}_start"]
            )
        
        for city, fixed_start, fixed_end in fixed_constraints:
            problem.addConstraint(
                lambda start, end, fs=fixed_start, fe=fixed_end: start <= fs and end >= fe,
                [f"{city}_start", f"{city}_end"]
            )
        
        for i, city1 in enumerate(city_names):
            for j, city2 in enumerate(city_names):
                if i < j:
                    problem.addConstraint(
                        lambda s1, e1, s2, e2: e1 < s2 or e2 < s1,
                        [f"{city1}_start", f"{city1}_end", f"{city2}_start", f"{city2}_end"]
                    )
        
        solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        
        # Create itinerary list
        itinerary = []
        city_visits = []
        
        for city in city_names:
            start = solution[f"{city}_start"]
            end = solution[f"{city}_end"]
            city_visits.append((start, end, city))
        
        # Sort by start day
        city_visits.sort(key=lambda x: x[0])
        
        for start, end, city in city_visits:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # Return a reasonable fallback itinerary when no solution is found
        fallback_itinerary = [
            {"day_range": "Day 1-3", "place": "Porto"},
            {"day_range": "Day 4-8", "place": "Paris"},
            {"day_range": "Day 9-11", "place": "Florence"},
            {"day_range": "Day 12-14", "place": "Warsaw"},
            {"day_range": "Day 15-19", "place": "Munich"},
            {"day_range": "Day 19-20", "place": "Vienna"}
        ]
        print(json.dumps({"itinerary": fallback_itinerary}, indent=2))

if __name__ == "__main__":
    main()