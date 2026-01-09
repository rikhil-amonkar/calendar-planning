import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()
    
    cities = ['Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich', 'Reykjavik']
    
    # Define variables for start day of each city visit
    start_days = {}
    for city in cities:
        start_days[city] = f"start_{city}"
    
    # Add variables with domain 1-25 (days)
    for var_name in start_days.values():
        problem.addVariable(var_name, range(1, 26))
    
    # Fixed constraints from the problem statement
    # Stuttgart: 4 days, conference on day 4 and day 7
    problem.addConstraint(lambda start_Stuttgart: start_Stuttgart <= 4 and start_Stuttgart + 3 >= 7, ['start_Stuttgart'])
    
    # Istanbul: 4 days, between day 19 and day 22
    problem.addConstraint(lambda start_Istanbul: start_Istanbul >= 19 and start_Istanbul <= 22, ['start_Istanbul'])
    
    # Munich: 3 days, annual show from day 13 to day 15
    problem.addConstraint(lambda start_Munich: start_Munich <= 13 and start_Munich + 2 >= 15, ['start_Munich'])
    
    # Reykjavik: 4 days, workshop between day 1 and day 4
    problem.addConstraint(lambda start_Reykjavik: start_Reykjavik <= 1 and start_Reykjavik + 3 >= 4, ['start_Reykjavik'])
    
    # Duration constraints
    durations = {
        'Stuttgart': 4,
        'Istanbul': 4, 
        'Vilnius': 4,
        'Seville': 3,
        'Geneva': 5,
        'Valencia': 5,
        'Munich': 3,
        'Reykjavik': 4
    }
    
    # No overlap constraint - cities cannot overlap in time
    for i, city1 in enumerate(cities):
        for j, city2 in enumerate(cities):
            if i < j:
                problem.addConstraint(
                    lambda start1, start2, city1=city1, city2=city2: 
                    start1 + durations[city1] <= start2 or start2 + durations[city2] <= start1,
                    [start_days[city1], start_days[city2]]
                )
    
    # Flight connectivity constraints
    direct_flights = [
        ('Geneva', 'Istanbul'),
        ('Reykjavik', 'Munich'),
        ('Stuttgart', 'Valencia'),
        ('Reykjavik', 'Stuttgart'),
        ('Stuttgart', 'Istanbul'),
        ('Munich', 'Geneva'),
        ('Istanbul', 'Vilnius'),
        ('Valencia', 'Seville'),
        ('Valencia', 'Istanbul'),
        ('Vilnius', 'Munich'),
        ('Seville', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Valencia', 'Geneva'),
        ('Valencia', 'Munich')
    ]
    
    # For consecutive cities, the end day of first must equal start day of second
    # We need to define the order of visits
    city_order = [f"order_{i}" for i in range(len(cities))]
    problem.addVariables(city_order, cities)
    problem.addConstraint(AllDifferentConstraint(), city_order)
    
    # Connectivity constraint between consecutive cities in the order
    for i in range(len(cities) - 1):
        problem.addConstraint(
            lambda city1, city2, start1, start2, dur1: 
            ((city1, city2) in direct_flights or (city2, city1) in direct_flights) and 
            (start1 + dur1 == start2),
            [city_order[i], city_order[i+1], start_days[city_order[i]], start_days[city_order[i+1]], durations[city_order[i]]]
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        
        # Create itinerary from solution
        itinerary = []
        city_visits = []
        
        for city in cities:
            start_day = solution[start_days[city]]
            end_day = start_day + durations[city] - 1
            city_visits.append({
                'city': city,
                'start': start_day,
                'end': end_day
            })
        
        # Sort by start day
        city_visits.sort(key=lambda x: x['start'])
        
        # Create final itinerary format
        for visit in city_visits:
            if visit['start'] == visit['end']:
                day_range = f"Day {visit['start']}"
            else:
                day_range = f"Day {visit['start']}-{visit['end']}"
            itinerary.append({
                'day_range': day_range,
                'place': visit['city']
            })
        
        # Output as JSON
        output = {'itinerary': itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()