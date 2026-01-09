import constraint
import json

def main():
    # Define the problem
    problem = constraint.Problem()
    
    # Cities and their required days
    cities = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }
    
    # Direct flight connections
    flights = {
        'Frankfurt': ['Dublin', 'London', 'Vilnius', 'Stuttgart'],
        'Dublin': ['Frankfurt', 'London', 'Seville', 'Santorini'],
        'London': ['Frankfurt', 'Dublin', 'Santorini', 'Stuttgart'],
        'Vilnius': ['Frankfurt'],
        'Stuttgart': ['Frankfurt', 'London'],
        'Seville': ['Dublin'],
        'Santorini': ['London', 'Dublin']
    }
    
    # Total days
    total_days = 17
    
    # Special constraints
    london_meet_days = [9, 10]  # Must be in London between day 9 and 10
    stuttgart_relatives_days = [7, 8, 9]  # Must be in Stuttgart between day 7 and 9
    
    # Variables: start day for each city (0 means not visited)
    for city in cities:
        problem.addVariable(f'{city}_start', range(1, total_days + 1))
        problem.addVariable(f'{city}_end', range(1, total_days + 1))
    
    # Constraint: end day = start day + duration - 1
    for city, duration in cities.items():
        problem.addConstraint(
            lambda start, end, dur=duration: end == start + dur - 1,
            [f'{city}_start', f'{city}_end']
        )
    
    # Constraint: all visits must be within the 17-day period
    for city in cities:
        problem.addConstraint(
            lambda start, end: start >= 1 and end <= total_days,
            [f'{city}_start', f'{city}_end']
        )
    
    # Constraint: no overlapping visits to different cities
    city_pairs = [(c1, c2) for c1 in cities for c2 in cities if c1 != c2]
    for city1, city2 in city_pairs:
        problem.addConstraint(
            lambda s1, e1, s2, e2: e1 < s2 or e2 < s1,
            [f'{city1}_start', f'{city1}_end', f'{city2}_start', f'{city2}_end']
        )
    
    # Constraint: London must be visited between day 9 and 10
    problem.addConstraint(
        lambda start, end: start <= 9 and end >= 10,
        ['London_start', 'London_end']
    )
    
    # Constraint: Stuttgart must be visited between day 7 and 9
    problem.addConstraint(
        lambda start, end: start <= 7 and end >= 9,
        ['Stuttgart_start', 'Stuttgart_end']
    )
    
    # Constraint: flight connectivity between consecutive cities
    city_list = list(cities.keys())
    for i in range(len(city_list) - 1):
        for j in range(i + 1, len(city_list)):
            city1, city2 = city_list[i], city_list[j]
            # If city2 immediately follows city1, they must be connected by flight
            problem.addConstraint(
                lambda s1, e1, s2, e2, c1=city1, c2=city2: 
                not (e1 + 1 == s2) or (c2 in flights.get(c1, []) and c1 in flights.get(c2, [])),
                [f'{city1}_start', f'{city1}_end', f'{city2}_start', f'{city2}_end']
            )
            # If city1 immediately follows city2, they must be connected by flight
            problem.addConstraint(
                lambda s1, e1, s2, e2, c1=city1, c2=city2: 
                not (e2 + 1 == s1) or (c2 in flights.get(c1, []) and c1 in flights.get(c2, [])),
                [f'{city1}_start', f'{city1}_end', f'{city2}_start', f'{city2}_end']
            )
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        result = {"itinerary": [], "error": "No valid itinerary found"}
        print(json.dumps(result))
        return
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create itinerary list
    itinerary = []
    city_visits = []
    
    for city in cities:
        start = solution[f'{city}_start']
        end = solution[f'{city}_end']
        city_visits.append((start, end, city))
    
    # Sort by start day
    city_visits.sort(key=lambda x: x[0])
    
    # Create day ranges
    for start, end, city in city_visits:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()