from constraint import Problem
import json

def main():
    problem = Problem()
    
    cities = ['Prague', 'Warsaw', 'Dublin', 'Athens', 'Vilnius', 'Porto', 'London', 'Seville', 'Lisbon', 'Dubrovnik']
    
    # Define durations for each city
    durations = {
        'Prague': 3,
        'Warsaw': 4, 
        'Dublin': 3,
        'Athens': 3,
        'Vilnius': 4,
        'Porto': 5,
        'London': 3,
        'Seville': 2,
        'Lisbon': 5,
        'Dubrovnik': 3
    }
    
    # Define fixed constraints
    fixed_constraints = [
        ('Prague', 1, 3),    # Prague between day 1-3
        ('Warsaw', 20, 23),  # Warsaw between day 20-23
        ('Porto', 16, 20),   # Porto between day 16-20
        ('London', 3, 5),    # London between day 3-5
        ('Lisbon', 5, 9)     # Lisbon between day 5-9
    ]
    
    # Define direct flight connections
    direct_flights = {
        'Warsaw': ['Vilnius', 'London', 'Athens', 'Lisbon', 'Porto', 'Prague', 'Dublin'],
        'Vilnius': ['Warsaw', 'Athens'],
        'Prague': ['Athens', 'Lisbon', 'London', 'Warsaw', 'Dublin'],
        'Athens': ['Prague', 'Vilnius', 'Dublin', 'Warsaw', 'Dubrovnik', 'London', 'Lisbon'],
        'London': ['Lisbon', 'Dublin', 'Prague', 'Warsaw', 'Athens'],
        'Lisbon': ['London', 'Porto', 'Prague', 'Athens', 'Warsaw', 'Dublin', 'Seville'],
        'Porto': ['Lisbon', 'Warsaw', 'Seville', 'Dublin'],
        'Dublin': ['London', 'Seville', 'Athens', 'Porto', 'Warsaw', 'Lisbon', 'Dubrovnik'],
        'Seville': ['Dublin', 'Porto', 'Lisbon'],
        'Dubrovnik': ['Athens', 'Dublin']
    }
    
    # Create variables for start day of each city visit
    for city in cities:
        problem.addVariable(f"start_{city}", range(1, 27))
    
    # Constraint: Total days must be 26
    def total_days_constraint(*starts):
        days_covered = set()
        for i, city in enumerate(cities):
            start = starts[i]
            duration = durations[city]
            for day in range(start, start + duration):
                if day > 26:
                    return False
                days_covered.add(day)
        return len(days_covered) == 26
    
    problem.addConstraint(total_days_constraint, [f"start_{city}" for city in cities])
    
    # Constraint: No overlapping stays
    def no_overlap_constraint(*starts):
        occupied_days = {}
        for i, city in enumerate(cities):
            start = starts[i]
            duration = durations[city]
            for day in range(start, start + duration):
                if day in occupied_days:
                    return False
                occupied_days[day] = city
        return True
    
    problem.addConstraint(no_overlap_constraint, [f"start_{city}" for city in cities])
    
    # Constraint: Fixed date requirements
    for city, start_day, end_day in fixed_constraints:
        problem.addConstraint(lambda start, s=start_day, e=end_day, d=durations[city]: start == s and start + d - 1 == e, 
                            [f"start_{city}"])
    
    # Constraint: Direct flight connections between consecutive cities
    def flight_connections_constraint(*starts):
        schedule = []
        for i, city in enumerate(cities):
            start = starts[i]
            duration = durations[city]
            schedule.append((start, start + duration - 1, city))
        
        schedule.sort()
        
        for i in range(len(schedule) - 1):
            current_city = schedule[i][2]
            next_city = schedule[i + 1][2]
            current_end = schedule[i][1]
            next_start = schedule[i + 1][0]
            
            # Cities must be connected by direct flight
            if next_city not in direct_flights.get(current_city, []):
                return False
            
            # Travel happens on the same day (end day of current = start day of next)
            if current_end + 1 != next_start:
                return False
        
        return True
    
    problem.addConstraint(flight_connections_constraint, [f"start_{city}" for city in cities])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    solution = solutions[0]
    
    # Build itinerary
    itinerary_items = []
    for city in cities:
        start = solution[f"start_{city}"]
        duration = durations[city]
        end = start + duration - 1
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary_items.append({"day_range": day_range, "place": city})
    
    # Sort by start day
    itinerary_items.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    result = {"itinerary": itinerary_items}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()