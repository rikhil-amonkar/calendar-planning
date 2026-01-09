import json
from constraint import Problem

def main():
    # Define cities and their required days
    cities = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # Define direct flight connections (bidirectional)
    direct_flights = [
        ('Helsinki', 'London'), ('Split', 'Madrid'), ('Helsinki', 'Madrid'),
        ('London', 'Madrid'), ('Brussels', 'London'), ('Bucharest', 'London'),
        ('Brussels', 'Bucharest'), ('Bucharest', 'Madrid'), ('Split', 'Helsinki'),
        ('Mykonos', 'Madrid'), ('Stuttgart', 'London'), ('Helsinki', 'Brussels'),
        ('Brussels', 'Madrid'), ('Split', 'London'), ('Stuttgart', 'Split'),
        ('London', 'Mykonos')
    ]
    
    # Make flights bidirectional
    bidirectional_flights = set()
    for city1, city2 in direct_flights:
        bidirectional_flights.add((city1, city2))
        bidirectional_flights.add((city2, city1))
    
    # Add self-connections (staying in the same city)
    for city in cities:
        bidirectional_flights.add((city, city))
    
    problem = Problem()
    
    # Create variables for start day of each city visit
    city_vars = {}
    for city in cities:
        city_vars[city] = f"start_{city}"
    
    # Add variables with domain (possible start days)
    total_days = 21
    for city, days_needed in cities.items():
        max_start = total_days - days_needed + 1
        problem.addVariable(city_vars[city], range(1, max_start + 1))
    
    # Constraint 1: All city visits must fit within the 21-day period
    # (Already handled by the variable domain)
    
    # Constraint 2: No overlapping visits - use a different approach
    # We'll ensure that all visits are sequential without gaps or overlaps
    def no_overlapping_visits(*starts):
        city_list = list(cities.keys())
        
        # Create intervals for each city
        intervals = []
        for i, start in enumerate(starts):
            end = start + cities[city_list[i]] - 1
            intervals.append((start, end))
        
        # Check if intervals are non-overlapping and cover exactly 21 days
        # Sort by start day
        intervals.sort()
        
        # Check for overlaps
        for i in range(len(intervals) - 1):
            current_end = intervals[i][1]
            next_start = intervals[i + 1][0]
            if next_start <= current_end:  # Overlap detected
                return False
        
        # Check if all days from 1 to 21 are covered
        occupied_days = set()
        for start, end in intervals:
            occupied_days.update(range(start, end + 1))
        
        return occupied_days == set(range(1, total_days + 1))
    
    problem.addConstraint(no_overlapping_visits, [city_vars[city] for city in cities])
    
    # Constraint 3: Stuttgart must be between day 1 and day 4
    def stuttgart_timing(stuttgart_start):
        days_needed = cities['Stuttgart']
        end_day = stuttgart_start + days_needed - 1
        return stuttgart_start >= 1 and end_day <= 4
    
    problem.addConstraint(stuttgart_timing, [city_vars['Stuttgart']])
    
    # Constraint 4: Madrid conference on days 20-21
    def madrid_conference_timing(madrid_start):
        days_needed = cities['Madrid']
        end_day = madrid_start + days_needed - 1
        return end_day >= 20  # Must end on day 20 or 21
    
    problem.addConstraint(madrid_conference_timing, [city_vars['Madrid']])
    
    # Constraint 5: Sequential cities must have direct flight connections
    def valid_flight_connections(*starts):
        city_list = list(cities.keys())
        
        # Create a list of (start_day, end_day, city) and sort by start day
        visits = []
        for i, start in enumerate(starts):
            city = city_list[i]
            end = start + cities[city] - 1
            visits.append((start, end, city))
        
        visits.sort()
        
        # Check transitions between consecutive visits
        for i in range(len(visits) - 1):
            current_end = visits[i][1]
            next_start = visits[i + 1][0]
            current_city = visits[i][2]
            next_city = visits[i + 1][2]
            
            # Visits should be consecutive (no gaps)
            if next_start != current_end + 1:
                return False
            
            # Check flight connection between consecutive cities
            if (current_city, next_city) not in bidirectional_flights:
                return False
        
        return True
    
    problem.addConstraint(valid_flight_connections, [city_vars[city] for city in cities])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create day ranges for each city
    itinerary = []
    
    for city in cities:
        start_day = solution[city_vars[city]]
        end_day = start_day + cities[city] - 1
        
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
    
    # Sort by start day
    itinerary.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()