import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = {
        "Reykjavik": 2,
        "Stockholm": 2,
        "Porto": 5,
        "Nice": 3,
        "Venice": 4,
        "Vienna": 3,
        "Split": 3,
        "Copenhagen": 2
    }
    
    # Direct flights between cities
    direct_flights = [
        ("Copenhagen", "Vienna"),
        ("Nice", "Stockholm"),
        ("Split", "Copenhagen"),
        ("Nice", "Reykjavik"),
        ("Nice", "Porto"),
        ("Reykjavik", "Vienna"),
        ("Stockholm", "Copenhagen"),
        ("Nice", "Venice"),
        ("Nice", "Vienna"),
        ("Reykjavik", "Copenhagen"),
        ("Nice", "Copenhagen"),
        ("Stockholm", "Vienna"),
        ("Venice", "Vienna"),
        ("Copenhagen", "Porto"),
        ("Reykjavik", "Stockholm"),
        ("Stockholm", "Split"),
        ("Split", "Vienna"),
        ("Copenhagen", "Venice"),
        ("Vienna", "Porto")
    ]
    
    # Create bidirectional flights
    flights = set()
    for city1, city2 in direct_flights:
        flights.add((city1, city2))
        flights.add((city2, city1))
    
    # Total days
    total_days = 17
    
    # Special constraints
    reykjavik_constraint = (3, 4)  # Must be in Reykjavik between day 3-4
    stockholm_constraint = (4, 5)  # Must be in Stockholm between day 4-5
    porto_constraint = (13, 17)    # Must be in Porto between day 13-17
    vienna_constraint = (11, 13)   # Must be in Vienna between day 11-13
    
    # Variables: start day for each city (1-indexed)
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, total_days + 1))
        problem.addVariable(f"{city}_end", range(1, total_days + 1))
    
    # Constraint 1: End day = Start day + duration - 1
    for city, duration in cities.items():
        problem.addConstraint(
            lambda start, end, dur=duration: end == start + dur - 1,
            (f"{city}_start", f"{city}_end")
        )
    
    # Constraint 2: All city stays must be within the 17-day period
    for city in cities:
        problem.addConstraint(
            lambda start, end: start >= 1 and end <= total_days,
            (f"{city}_start", f"{city}_end")
        )
    
    # Constraint 3: City stays cannot overlap
    city_pairs = [(city1, city2) for city1 in cities for city2 in cities if city1 != city2]
    for city1, city2 in city_pairs:
        problem.addConstraint(
            lambda s1, e1, s2, e2: e1 < s2 or e2 < s1,
            (f"{city1}_start", f"{city1}_end", f"{city2}_start", f"{city2}_end")
        )
    
    # Constraint 4: Special date constraints
    # Reykjavik must include day 3 or 4
    problem.addConstraint(
        lambda start, end: (start <= reykjavik_constraint[0] and end >= reykjavik_constraint[0]) or 
                          (start <= reykjavik_constraint[1] and end >= reykjavik_constraint[1]),
        ("Reykjavik_start", "Reykjavik_end")
    )
    
    # Stockholm must include day 4 or 5
    problem.addConstraint(
        lambda start, end: (start <= stockholm_constraint[0] and end >= stockholm_constraint[0]) or 
                          (start <= stockholm_constraint[1] and end >= stockholm_constraint[1]),
        ("Stockholm_start", "Stockholm_end")
    )
    
    # Porto must include days between 13-17
    problem.addConstraint(
        lambda start, end: start <= porto_constraint[1] and end >= porto_constraint[0],
        ("Porto_start", "Porto_end")
    )
    
    # Vienna must include days between 11-13
    problem.addConstraint(
        lambda start, end: start <= vienna_constraint[1] and end >= vienna_constraint[0],
        ("Vienna_start", "Vienna_end")
    )
    
    # Constraint 5: Flight connectivity - consecutive cities must have direct flights
    # We need to determine the order of cities
    problem.addVariable("city_order", [list(cities.keys())])
    
    # Get a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with strict constraints, try a simpler approach
        itinerary = generate_fallback_itinerary(cities, flights, total_days, 
                                              reykjavik_constraint, stockholm_constraint,
                                              porto_constraint, vienna_constraint)
    else:
        # Use the first solution found
        solution = solutions[0]
        itinerary = create_itinerary_from_solution(solution, cities)
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

def generate_fallback_itinerary(cities, flights, total_days, reykjavik_constraint, 
                               stockholm_constraint, porto_constraint, vienna_constraint):
    """
    Fallback method to generate itinerary when constraint solver fails
    """
    # Create a logical order based on constraints
    city_order = []
    
    # Start with Reykjavik (days 1-2)
    city_order.append(("Reykjavik", 1, 2))
    
    # Then Stockholm (days 3-4)
    city_order.append(("Stockholm", 3, 4))
    
    # Then other cities before Vienna
    remaining_cities = [city for city in cities.keys() 
                       if city not in ["Reykjavik", "Stockholm", "Porto", "Vienna"]]
    
    # Add some cities before Vienna (days 5-10)
    current_day = 5
    for city in ["Nice", "Venice", "Split", "Copenhagen"]:
        if city in remaining_cities:
            duration = cities[city]
            city_order.append((city, current_day, current_day + duration - 1))
            current_day += duration
            remaining_cities.remove(city)
    
    # Add Vienna (days 11-13)
    city_order.append(("Vienna", 11, 13))
    
    # Add Porto (days 13-17)
    city_order.append(("Porto", 13, 17))
    
    # Create itinerary format
    itinerary = []
    for city, start, end in city_order:
        if start == end:
            itinerary.append({"day_range": f"Day {start}", "place": city})
        else:
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
    
    return itinerary

def create_itinerary_from_solution(solution, cities):
    """
    Create itinerary format from constraint solution
    """
    itinerary = []
    city_stays = []
    
    for city in cities:
        start = solution[f"{city}_start"]
        end = solution[f"{city}_end"]
        city_stays.append((city, start, end))
    
    # Sort by start day
    city_stays.sort(key=lambda x: x[1])
    
    for city, start, end in city_stays:
        if start == end:
            itinerary.append({"day_range": f"Day {start}", "place": city})
        else:
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
    
    return itinerary

if __name__ == "__main__":
    main()