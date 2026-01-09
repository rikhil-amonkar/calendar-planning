import json
from constraint import Problem, AllDifferentConstraint

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
    
    # Define direct flight connections
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
    
    # Constraint: All visits must be non-overlapping
    def no_overlap(*starts):
        city_list = list(cities.keys())
        intervals = []
        for i, start in enumerate(starts):
            end = start + cities[city_list[i]] - 1
            intervals.append((start, end))
        
        # Check for overlaps
        intervals.sort()
        for i in range(len(intervals) - 1):
            if intervals[i][1] >= intervals[i+1][0]:
                return False
        return True
    
    problem.addConstraint(no_overlap, [city_vars[city] for city in cities])
    
    # Constraint: All days from 1 to 21 must be covered (no gaps)
    def no_gaps(*starts):
        city_list = list(cities.keys())
        days_covered = set()
        for i, start in enumerate(starts):
            days_needed = cities[city_list[i]]
            for day in range(start, start + days_needed):
                days_covered.add(day)
        
        # Check if all days 1-21 are covered
        return len(days_covered) == total_days and min(days_covered) == 1 and max(days_covered) == total_days
    
    problem.addConstraint(no_gaps, [city_vars[city] for city in cities])
    
    # Constraint: Stuttgart must be between day 1 and day 4
    def stuttgart_timing(stuttgart_start):
        days_needed = cities['Stuttgart']
        end_day = stuttgart_start + days_needed - 1
        return stuttgart_start >= 1 and end_day <= 4
    
    problem.addConstraint(stuttgart_timing, [city_vars['Stuttgart']])
    
    # Constraint: Madrid conference on days 20-21
    def madrid_conference_timing(madrid_start):
        days_needed = cities['Madrid']
        end_day = madrid_start + days_needed - 1
        return end_day >= 20  # Must end on day 20 or 21
    
    problem.addConstraint(madrid_conference_timing, [city_vars['Madrid']])
    
    # Constraint: Sequential cities must have direct flight connections
    def valid_flight_connections(*starts):
        city_list = list(cities.keys())
        
        # Create a mapping of which city is visited on each day
        day_to_city = {}
        for i, start in enumerate(starts):
            city = city_list[i]
            for day in range(start, start + cities[city]):
                day_to_city[day] = city
        
        # Check transitions between consecutive days
        for day in range(1, total_days):
            current_city = day_to_city.get(day)
            next_city = day_to_city.get(day + 1)
            
            # If we're changing cities, check if there's a direct flight
            if current_city != next_city:
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
    day_assignment = {}
    
    for city in cities:
        start_day = solution[city_vars[city]]
        end_day = start_day + cities[city] - 1
        
        # Store which days this city occupies
        for day in range(start_day, end_day + 1):
            day_assignment[day] = city
        
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