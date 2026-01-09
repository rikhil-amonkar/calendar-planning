import json
from constraint import Problem

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities
    cities = ['London', 'Oslo', 'Split', 'Porto']
    
    # Total days
    total_days = 16
    
    # Define variables for start day of each city visit
    # London must start on day 1
    problem.addVariable('London_start', [1])
    
    # Oslo can start after London ends (day 8 or later)
    problem.addVariable('Oslo_start', range(8, total_days + 1))
    
    # Split must include days 7-11
    # Split can start on day 3-7 (since it needs 5 days and must include days 7-11)
    problem.addVariable('Split_start', range(3, 8))
    
    # Porto can start after Oslo ends
    problem.addVariable('Porto_start', range(1, total_days + 1))
    
    # Duration variables (fixed)
    london_duration = 7
    oslo_duration = 2
    split_duration = 5
    porto_duration = 5
    
    # No overlap constraint
    def no_overlap(london_s, oslo_s, split_s, porto_s):
        # Calculate end days
        london_e = london_s + london_duration - 1
        oslo_e = oslo_s + oslo_duration - 1
        split_e = split_s + split_duration - 1
        porto_e = porto_s + porto_duration - 1
        
        visits = [
            (london_s, london_e),
            (oslo_s, oslo_e),
            (split_s, split_e),
            (porto_s, porto_e)
        ]
        
        # Check for overlaps
        for i in range(len(visits)):
            for j in range(i + 1, len(visits)):
                start1, end1 = visits[i]
                start2, end2 = visits[j]
                if not (end1 < start2 or end2 < start1):
                    return False
        
        # Check all days are covered exactly once
        covered_days = set()
        for start, end in visits:
            covered_days.update(range(start, end + 1))
        
        return (len(covered_days) == total_days and 
                min(covered_days) == 1 and 
                max(covered_days) == total_days)
    
    problem.addConstraint(no_overlap, ['London_start', 'Oslo_start', 'Split_start', 'Porto_start'])
    
    # Flight connectivity constraints
    def valid_flight_sequence(london_s, oslo_s, split_s, porto_s):
        # Get visit order by start day
        visits = [
            ('London', london_s, london_s + london_duration - 1),
            ('Oslo', oslo_s, oslo_s + oslo_duration - 1),
            ('Split', split_s, split_s + split_duration - 1),
            ('Porto', porto_s, porto_s + porto_duration - 1)
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
    
    problem.addConstraint(valid_flight_sequence, ['London_start', 'Oslo_start', 'Split_start', 'Porto_start'])
    
    # Additional constraints
    # Split must include days 7-11
    def split_includes_show(split_s):
        split_e = split_s + split_duration - 1
        return split_s <= 7 and split_e >= 11
    
    problem.addConstraint(split_includes_show, ['Split_start'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create itinerary
    itinerary = []
    visits = [
        ('London', solution['London_start'], solution['London_start'] + london_duration - 1),
        ('Oslo', solution['Oslo_start'], solution['Oslo_start'] + oslo_duration - 1),
        ('Split', solution['Split_start'], solution['Split_start'] + split_duration - 1),
        ('Porto', solution['Porto_start'], solution['Porto_start'] + porto_duration - 1)
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