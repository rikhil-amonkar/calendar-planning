import constraint
import json

def main():
    # Define the problem
    problem = constraint.Problem()
    
    # Cities and their required days
    cities = ['Brussels', 'Venice', 'Madrid', 'London', 'Lisbon', 'Reykjavik', 'Santorini']
    required_days = {
        'Brussels': 2,
        'Venice': 3,
        'Madrid': 5,
        'London': 3,
        'Lisbon': 4,
        'Reykjavik': 3,
        'Santorini': 3
    }
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Venice', 'Madrid'),
        ('Lisbon', 'Reykjavik'),
        ('Brussels', 'Venice'),
        ('Venice', 'Santorini'),
        ('Lisbon', 'Venice'),
        ('Reykjavik', 'Madrid'),
        ('Brussels', 'London'),
        ('Madrid', 'London'),
        ('Santorini', 'London'),
        ('London', 'Reykjavik'),
        ('Brussels', 'Lisbon'),
        ('Lisbon', 'London'),
        ('Lisbon', 'Madrid'),
        ('Madrid', 'Santorini'),
        ('Brussels', 'Reykjavik'),
        ('Brussels', 'Madrid'),
        ('Venice', 'London')
    ]
    
    # Create bidirectional flights
    all_flights = set()
    for city1, city2 in direct_flights:
        all_flights.add((city1, city2))
        all_flights.add((city2, city1))
    
    # Fixed constraints
    # Day 1-2: Brussels (conference)
    # Day 5-7: Venice (relatives) 
    # Day 7-11: Madrid (wedding)
    
    # We need to assign cities to days 1-17
    # Each day variable represents which city we're in on that day
    total_days = 17
    
    # Add variables for each day (1 to 17)
    for day in range(1, total_days + 1):
        problem.addVariable(f'day_{day}', cities)
    
    # Constraint 1: Brussels on days 1-2
    problem.addConstraint(lambda d1, d2: d1 == 'Brussels' and d2 == 'Brussels', 
                         ['day_1', 'day_2'])
    
    # Constraint 2: Venice on at least one of days 5,6,7 (relatives visit)
    problem.addConstraint(lambda d5, d6, d7: 'Venice' in [d5, d6, d7],
                         ['day_5', 'day_6', 'day_7'])
    
    # Constraint 3: Madrid on days 7-11 (wedding)
    problem.addConstraint(lambda d7, d8, d9, d10, d11: 
                         d7 == 'Madrid' and d8 == 'Madrid' and d9 == 'Madrid' and 
                         d10 == 'Madrid' and d11 == 'Madrid',
                         ['day_7', 'day_8', 'day_9', 'day_10', 'day_11'])
    
    # Constraint 4: Only direct flights allowed between consecutive days
    for day in range(1, total_days):
        def valid_transition(current_city, next_city):
            if current_city == next_city:
                return True  # Staying in same city
            return (current_city, next_city) in all_flights
        
        problem.addConstraint(valid_transition, [f'day_{day}', f'day_{day+1}'])
    
    # Constraint 5: Total days in each city must match requirements
    def check_total_days(*days):
        day_counts = {city: 0 for city in cities}
        for city in days:
            day_counts[city] += 1
        
        for city, required in required_days.items():
            if day_counts[city] != required:
                return False
        return True
    
    problem.addConstraint(check_total_days, [f'day_{i}' for i in range(1, total_days + 1)])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Convert to itinerary format
    itinerary = []
    current_city = solution['day_1']
    start_day = 1
    
    for day in range(2, total_days + 1):
        if solution[f'day_{day}'] != current_city:
            # End of stay in current city
            end_day = day - 1
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": current_city})
            
            current_city = solution[f'day_{day}']
            start_day = day
    
    # Add the last stay
    end_day = total_days
    if start_day == end_day:
        day_range = f"Day {start_day}"
    else:
        day_range = f"Day {start_day}-{end_day}"
    itinerary.append({"day_range": day_range, "place": current_city})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()