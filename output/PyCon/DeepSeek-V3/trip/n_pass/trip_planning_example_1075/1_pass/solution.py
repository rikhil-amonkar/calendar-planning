import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    problem = Problem()
    
    # Cities and their required days
    cities = {
        'Vienna': 4,
        'Lyon': 3,
        'Edinburgh': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Manchester': 2,
        'Split': 5,
        'Prague': 4
    }
    
    # Direct flight connections
    flights = {
        'Reykjavik': ['Stuttgart', 'Vienna', 'Prague'],
        'Stuttgart': ['Reykjavik', 'Split', 'Vienna', 'Edinburgh', 'Manchester'],
        'Prague': ['Manchester', 'Edinburgh', 'Vienna', 'Split', 'Lyon', 'Reykjavik'],
        'Manchester': ['Prague', 'Split', 'Vienna', 'Stuttgart'],
        'Edinburgh': ['Prague', 'Stuttgart'],
        'Vienna': ['Stuttgart', 'Manchester', 'Lyon', 'Split', 'Reykjavik', 'Prague'],
        'Split': ['Stuttgart', 'Manchester', 'Lyon', 'Vienna', 'Prague'],
        'Lyon': ['Vienna', 'Split', 'Prague']
    }
    
    # Special constraints
    edinburgh_show = (5, 8)  # Days 5-8 in Edinburgh
    split_wedding = (19, 23)  # Days 19-23 in Split
    
    total_days = 25
    
    # Create variables for start day of each city visit
    city_vars = list(cities.keys())
    
    # Add variables for start days (1 to 25)
    for city in city_vars:
        problem.addVariable(city, range(1, total_days + 1))
    
    # Constraint 1: All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), city_vars)
    
    # Constraint 2: Total days must be exactly 25
    def total_days_constraint(*starts):
        days_used = set()
        for city, start in zip(city_vars, starts):
            duration = cities[city]
            for day in range(start, start + duration):
                if day > total_days:
                    return False
                days_used.add(day)
        return len(days_used) == total_days and max(days_used) == total_days
    
    problem.addConstraint(total_days_constraint, city_vars)
    
    # Constraint 3: No overlapping visits
    def no_overlap(*starts):
        intervals = []
        for city, start in zip(city_vars, starts):
            duration = cities[city]
            intervals.append((start, start + duration - 1))
        
        intervals.sort()
        for i in range(len(intervals) - 1):
            if intervals[i][1] >= intervals[i + 1][0]:
                return False
        return True
    
    problem.addConstraint(no_overlap, city_vars)
    
    # Constraint 4: Edinburgh show constraint
    problem.addConstraint(lambda e: e <= edinburgh_show[0] and e + cities['Edinburgh'] - 1 >= edinburgh_show[1], ['Edinburgh'])
    
    # Constraint 5: Split wedding constraint
    problem.addConstraint(lambda s: s <= split_wedding[0] and s + cities['Split'] - 1 >= split_wedding[1], ['Split'])
    
    # Constraint 6: Flight connectivity between consecutive cities
    def flight_connectivity(*starts):
        # Create list of (start_day, city, duration)
        visits = []
        for city, start in zip(city_vars, starts):
            visits.append((start, city, cities[city]))
        
        # Sort by start day
        visits.sort()
        
        # Check flight connectivity between consecutive cities
        for i in range(len(visits) - 1):
            current_city = visits[i][1]
            next_city = visits[i + 1][1]
            if next_city not in flights[current_city]:
                return False
        return True
    
    problem.addConstraint(flight_connectivity, city_vars)
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first solution
    solution = solutions[0]
    
    # Create itinerary with day ranges
    itinerary = []
    visits = []
    
    for city in city_vars:
        start = solution[city]
        duration = cities[city]
        end = start + duration - 1
        visits.append((start, end, city))
    
    # Sort by start day
    visits.sort()
    
    for start, end, city in visits:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))