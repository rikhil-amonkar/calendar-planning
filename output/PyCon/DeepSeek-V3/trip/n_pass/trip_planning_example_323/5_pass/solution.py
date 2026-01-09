import json
from constraint import Problem

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their durations
    cities = ['London', 'Oslo', 'Split', 'Porto']
    durations = {
        'London': 7,
        'Oslo': 2,
        'Split': 5,
        'Porto': 5
    }
    
    # Total days
    total_days = 16
    
    # Define variables for start day of each city visit
    # London must start on day 1
    problem.addVariable('London', [1])
    
    # Oslo can start after London ends (day 8 or later) but must end by day 16
    problem.addVariable('Oslo', range(8, total_days - durations['Oslo'] + 2))
    
    # Split must include days 7-11, so it must start on day 3, 4, 5, 6, or 7
    # But it must end by day 16
    problem.addVariable('Split', range(3, min(8, total_days - durations['Split'] + 2)))
    
    # Porto can start after Oslo ends, and must fit within 16 days
    problem.addVariable('Porto', range(1, total_days - durations['Porto'] + 2))
    
    # No overlap constraint - simplified version
    def no_overlap(london_s, oslo_s, split_s, porto_s):
        # Calculate end days
        london_e = london_s + durations['London'] - 1
        oslo_e = oslo_s + durations['Oslo'] - 1
        split_e = split_s + durations['Split'] - 1
        porto_e = porto_s + durations['Porto'] - 1
        
        # Check for overlaps
        intervals = [
            (london_s, london_e),
            (oslo_s, oslo_e),
            (split_s, split_e),
            (porto_s, porto_e)
        ]
        
        # Check all intervals are disjoint
        for i in range(len(intervals)):
            for j in range(i + 1, len(intervals)):
                s1, e1 = intervals[i]
                s2, e2 = intervals[j]
                if not (e1 < s2 or e2 < s1):
                    return False
        
        return True
    
    problem.addConstraint(no_overlap, ['London', 'Oslo', 'Split', 'Porto'])
    
    # Flight connectivity constraints
    def valid_flight_sequence(london_s, oslo_s, split_s, porto_s):
        # Get visits with start days and calculate end days
        visits = [
            ('London', london_s, london_s + durations['London'] - 1),
            ('Oslo', oslo_s, oslo_s + durations['Oslo'] - 1),
            ('Split', split_s, split_s + durations['Split'] - 1),
            ('Porto', porto_s, porto_s + durations['Porto'] - 1)
        ]
        
        # Sort by start day to get travel sequence
        visits.sort(key=lambda x: x[1])
        
        # Check direct flights between consecutive cities in the travel sequence
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
    
    problem.addConstraint(valid_flight_sequence, ['London', 'Oslo', 'Split', 'Porto'])
    
    # Split must include days 7-11
    def split_includes_show(split_s):
        split_e = split_s + durations['Split'] - 1
        return split_s <= 7 and split_e >= 11
    
    problem.addConstraint(split_includes_show, ['Split'])
    
    # Additional constraint: All days must be covered exactly once
    def all_days_covered(london_s, oslo_s, split_s, porto_s):
        # Calculate end days
        london_e = london_s + durations['London'] - 1
        oslo_e = oslo_s + durations['Oslo'] - 1
        split_e = split_s + durations['Split'] - 1
        porto_e = porto_s + durations['Porto'] - 1
        
        # Create set of all days covered
        all_days = set()
        for start, end in [(london_s, london_e), (oslo_s, oslo_e), 
                          (split_s, split_e), (porto_s, porto_e)]:
            all_days.update(range(start, end + 1))
        
        return len(all_days) == total_days and min(all_days) == 1 and max(all_days) == total_days
    
    problem.addConstraint(all_days_covered, ['London', 'Oslo', 'Split', 'Porto'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create itinerary
    itinerary = []
    visits = [
        ('London', solution['London'], solution['London'] + durations['London'] - 1),
        ('Oslo', solution['Oslo'], solution['Oslo'] + durations['Oslo'] - 1),
        ('Split', solution['Split'], solution['Split'] + durations['Split'] - 1),
        ('Porto', solution['Porto'], solution['Porto'] + durations['Porto'] - 1)
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