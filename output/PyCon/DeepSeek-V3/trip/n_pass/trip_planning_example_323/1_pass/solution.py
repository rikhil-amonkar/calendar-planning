import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities
    cities = ['London', 'Oslo', 'Split', 'Porto']
    
    # Total days
    total_days = 16
    
    # Define variables for start day of each city visit
    # We'll use -1 to indicate the city is not visited
    problem.addVariable('London_start', range(1, total_days + 1))
    problem.addVariable('Oslo_start', range(1, total_days + 1))
    problem.addVariable('Split_start', range(1, total_days + 1))
    problem.addVariable('Porto_start', range(1, total_days + 1))
    
    # Duration variables
    problem.addVariable('London_duration', range(1, total_days + 1))
    problem.addVariable('Oslo_duration', range(1, total_days + 1))
    problem.addVariable('Split_duration', range(1, total_days + 1))
    problem.addVariable('Porto_duration', range(1, total_days + 1))
    
    # Fixed constraints
    # Split: 5 days total, with show from day 7 to 11
    problem.addConstraint(lambda s, d: d == 5, ['Split_start', 'Split_duration'])
    problem.addConstraint(lambda s: s <= 7 and s + 5 - 1 >= 11, ['Split_start'])
    
    # Oslo: 2 days
    problem.addConstraint(lambda s, d: d == 2, ['Oslo_start', 'Oslo_duration'])
    
    # London: 7 days, between day 1 and 7
    problem.addConstraint(lambda s, d: d == 7, ['London_start', 'London_duration'])
    problem.addConstraint(lambda s: s == 1, ['London_start'])
    
    # Porto: 5 days
    problem.addConstraint(lambda s, d: d == 5, ['Porto_start', 'Porto_duration'])
    
    # All cities must be visited exactly once with their specified durations
    def no_overlap(london_s, london_d, oslo_s, oslo_d, split_s, split_d, porto_s, porto_d):
        visits = [
            (london_s, london_s + london_d - 1),
            (oslo_s, oslo_s + oslo_d - 1),
            (split_s, split_s + split_d - 1),
            (porto_s, porto_s + porto_d - 1)
        ]
        
        # Check for overlaps
        for i in range(len(visits)):
            for j in range(i + 1, len(visits)):
                start1, end1 = visits[i]
                start2, end2 = visits[j]
                if not (end1 < start2 or end2 < start1):
                    return False
        
        # Check all days are covered
        covered_days = set()
        for start, end in visits:
            covered_days.update(range(start, end + 1))
        
        return len(covered_days) == total_days and min(covered_days) == 1 and max(covered_days) == total_days
    
    problem.addConstraint(no_overlap, 
                         ['London_start', 'London_duration', 
                          'Oslo_start', 'Oslo_duration',
                          'Split_start', 'Split_duration',
                          'Porto_start', 'Porto_duration'])
    
    # Flight connectivity constraints
    def valid_flight_sequence(london_s, london_d, oslo_s, oslo_d, split_s, split_d, porto_s, porto_d):
        # Get visit order by start day
        visits = [
            ('London', london_s, london_s + london_d - 1),
            ('Oslo', oslo_s, oslo_s + oslo_d - 1),
            ('Split', split_s, split_s + split_d - 1),
            ('Porto', porto_s, porto_s + porto_d - 1)
        ]
        visits.sort(key=lambda x: x[1])  # Sort by start day
        
        # Check direct flights between consecutive cities
        flight_routes = {
            'London': ['Oslo', 'Split'],
            'Oslo': ['London', 'Split', 'Porto'],
            'Split': ['London', 'Oslo'],
            'Porto': ['Oslo']
        }
        
        for i in range(len(visits) - 1):
            current_city = visits[i][0]
            next_city = visits[i + 1][0]
            if next_city not in flight_routes[current_city]:
                return False
        
        return True
    
    problem.addConstraint(valid_flight_sequence,
                         ['London_start', 'London_duration',
                          'Oslo_start', 'Oslo_duration',
                          'Split_start', 'Split_duration',
                          'Porto_start', 'Porto_duration'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create itinerary
    itinerary = []
    visits = [
        ('London', solution['London_start'], solution['London_start'] + solution['London_duration'] - 1),
        ('Oslo', solution['Oslo_start'], solution['Oslo_start'] + solution['Oslo_duration'] - 1),
        ('Split', solution['Split_start'], solution['Split_start'] + solution['Split_duration'] - 1),
        ('Porto', solution['Porto_start'], solution['Porto_start'] + solution['Porto_duration'] - 1)
    ]
    
    # Sort by start day
    visits.sort(key=lambda x: x[1])
    
    for city, start, end in visits:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))