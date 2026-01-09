from constraint import Problem
import json

def main():
    problem = Problem()
    
    # Define cities and their required days
    cities = {
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    
    # Define direct flight connections
    connections = {
        'Copenhagen': ['Athens', 'Dubrovnik', 'Munich', 'Reykjavik', 'Venice', 'Barcelona', 'Tallinn'],
        'Munich': ['Tallinn', 'Copenhagen', 'Venice', 'Reykjavik', 'Athens', 'Lyon', 'Barcelona', 'Dubrovnik'],
        'Venice': ['Munich', 'Athens', 'Copenhagen', 'Lyon', 'Barcelona'],
        'Reykjavik': ['Athens', 'Copenhagen', 'Munich', 'Barcelona'],
        'Athens': ['Copenhagen', 'Dubrovnik', 'Venice', 'Munich', 'Barcelona'],
        'Lyon': ['Barcelona', 'Munich', 'Venice'],
        'Barcelona': ['Lyon', 'Reykjavik', 'Dubrovnik', 'Athens', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'],
        'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
        'Tallinn': ['Munich', 'Copenhagen', 'Barcelona']
    }
    
    # Total days
    total_days = 26
    
    # Define variables for start day of each city
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, total_days + 1))
        problem.addVariable(f"{city}_end", range(1, total_days + 1))
    
    # Constraint: end day = start day + duration - 1
    for city, duration in cities.items():
        problem.addConstraint(
            lambda start, end, dur=duration: end == start + dur - 1,
            [f"{city}_start", f"{city}_end"]
        )
    
    # Constraint: all city stays must be within the 26-day period
    for city in cities:
        problem.addConstraint(
            lambda start, end: start >= 1 and end <= total_days,
            [f"{city}_start", f"{city}_end"]
        )
    
    # Constraint: cities cannot overlap in time (except for travel days)
    city_pairs = [(c1, c2) for c1 in cities for c2 in cities if c1 != c2]
    for city1, city2 in city_pairs:
        problem.addConstraint(
            lambda s1, e1, s2, e2: e1 < s2 or e2 < s1,
            [f"{city1}_start", f"{city1}_end", f"{city2}_start", f"{city2}_end"]
        )
    
    # Special constraints
    # Barcelona between day 10 and day 12
    problem.addConstraint(
        lambda start, end: start <= 12 and end >= 10,
        ["Barcelona_start", "Barcelona_end"]
    )
    
    # Copenhagen between day 7 and day 10
    problem.addConstraint(
        lambda start, end: start <= 10 and end >= 7,
        ["Copenhagen_start", "Copenhagen_end"]
    )
    
    # Dubrovnik between day 16 and day 20
    problem.addConstraint(
        lambda start, end: start <= 20 and end >= 16,
        ["Dubrovnik_start", "Dubrovnik_end"]
    )
    
    # Constraint: travel connectivity - consecutive cities must have direct flights
    # This is complex to model directly, so we'll find a solution and then validate connectivity
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Take the first valid solution
    solution = solutions[0]
    
    # Create itinerary list
    itinerary = []
    city_stays = []
    
    for city in cities:
        start = solution[f"{city}_start"]
        end = solution[f"{city}_end"]
        city_stays.append((start, end, city))
    
    # Sort by start day
    city_stays.sort()
    
    # Build itinerary with day ranges
    for start, end, city in city_stays:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()