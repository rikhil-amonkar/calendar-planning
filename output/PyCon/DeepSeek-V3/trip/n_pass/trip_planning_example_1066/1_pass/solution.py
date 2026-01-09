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
    
    # Special constraints
    stuttgart_constraint = (1, 4)  # Stuttgart between day 1 and day 4
    madrid_conference = (20, 21)   # Madrid conference on days 20-21
    
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
    
    # Constraint: All visits must be non-overlapping and sequential
    def no_overlap(*starts):
        city_list = list(cities.keys())
        for i in range(len(starts)):
            for j in range(i + 1, len(starts)):
                start_i = starts[i]
                start_j = starts[j]
                days_i = cities[city_list[i]]
                days_j = cities[city_list[j]]
                
                # Check if visits overlap
                if not (start_i + days_i <= start_j or start_j + days_j <= start_i):
                    return False
        return True
    
    problem.addConstraint(no_overlap, [city_vars[city] for city in cities])
    
    # Constraint: Total days must be exactly 21
    def total_days_constraint(*starts):
        city_list = list(cities.keys())
        days_covered = set()
        for i, start in enumerate(starts):
            days_needed = cities[city_list[i]]
            for day in range(start, start + days_needed):
                days_covered.add(day)
        return len(days_covered) == total_days and min(days_covered) == 1 and max(days_covered) == total_days
    
    problem.addConstraint(total_days_constraint, [city_vars[city] for city in cities])
    
    # Constraint: Stuttgart must be between day 1 and day 4
    def stuttgart_timing(stuttgart_start):
        days_needed = cities['Stuttgart']
        return (stuttgart_start >= stuttgart_constraint[0] and 
                stuttgart_start + days_needed - 1 <= stuttgart_constraint[1])
    
    problem.addConstraint(stuttgart_timing, [city_vars['Stuttgart']])
    
    # Constraint: Madrid conference on days 20-21
    def madrid_conference_timing(madrid_start):
        days_needed = cities['Madrid']
        return madrid_start + days_needed - 1 >= madrid_conference[0]
    
    problem.addConstraint(madrid_conference_timing, [city_vars['Madrid']])
    
    # Constraint: Sequential flights must be connected
    def valid_flight_sequence(*starts):
        city_list = list(cities.keys())
        
        # Create day-to-city mapping
        day_city = {}
        for i, start in enumerate(starts):
            city = city_list[i]
            days_needed = cities[city]
            for day in range(start, start + days_needed):
                day_city[day] = city
        
        # Check transitions between consecutive days
        for day in range(1, total_days):
            current_city = day_city.get(day)
            next_city = day_city.get(day + 1)
            
            if current_city != next_city:
                # This is a travel day - check if direct flight exists
                if (current_city, next_city) not in bidirectional_flights:
                    return False
        
        return True
    
    problem.addConstraint(valid_flight_sequence, [city_vars[city] for city in cities])
    
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