import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Lisbon': 3,
        'Vilnius': 4,
        'Oslo': 3
    }
    
    # Direct flights between cities
    direct_flights = {
        'Riga': ['Oslo', 'Rome', 'Milan', 'Vienna', 'Vilnius', 'Lisbon'],
        'Oslo': ['Riga', 'Rome', 'Lisbon', 'Vienna', 'Vilnius', 'Milan'],
        'Rome': ['Oslo', 'Riga', 'Lisbon', 'Vienna'],
        'Vienna': ['Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'],
        'Milan': ['Vienna', 'Riga', 'Oslo', 'Lisbon', 'Vilnius'],
        'Lisbon': ['Vienna', 'Oslo', 'Rome', 'Riga', 'Milan'],
        'Vilnius': ['Vienna', 'Oslo', 'Riga', 'Milan']
    }
    
    # Special constraints
    # Vienna: conference on day 1 and day 4
    # Lisbon: relatives between day 11 and day 13
    # Oslo: friend between day 13 and day 15
    
    # Create variables for start day of each city visit
    # We'll use the constraint that cities must be visited in sequence
    city_names = list(cities.keys())
    
    # Add variables for order (1-7) and start day (1-15)
    for city in city_names:
        problem.addVariable(f'{city}_order', range(1, 8))
        problem.addVariable(f'{city}_start', range(1, 16))
    
    # All cities must have different orders
    problem.addConstraint(AllDifferentConstraint(), [f'{city}_order' for city in city_names])
    
    # Duration constraints
    for city in city_names:
        duration = cities[city]
        
        def duration_constraint(start, order_vars, city_name=city, dur=duration):
            # Ensure the visit doesn't exceed day 15
            return start + dur - 1 <= 15
        
        problem.addConstraint(duration_constraint, [f'{city}_start'])
    
    # No overlap constraint
    for i, city1 in enumerate(city_names):
        for city2 in city_names[i+1:]:
            def no_overlap(start1, start2, dur1=cities[city1], dur2=cities[city2]):
                return (start1 + dur1 <= start2) or (start2 + dur2 <= start1)
            
            problem.addConstraint(no_overlap, [f'{city1}_start', f'{city2}_start'])
    
    # Flight connectivity constraint
    def flight_connectivity(order_vars, start_vars, flights=direct_flights):
        # Reconstruct the visit sequence from order variables
        city_orders = []
        for city in city_names:
            city_orders.append((order_vars[city_names.index(city)], city, start_vars[city_names.index(city)]))
        
        # Sort by order
        city_orders.sort()
        
        # Check if consecutive cities in sequence have direct flights
        for i in range(len(city_orders) - 1):
            city1 = city_orders[i][1]
            city2 = city_orders[i + 1][1]
            
            if city2 not in flights[city1]:
                return False
        
        return True
    
    problem.addConstraint(flight_connectivity, 
                         [f'{city}_order' for city in city_names] + [f'{city}_start' for city in city_names])
    
    # Special date constraints
    # Vienna must include day 1 and day 4
    def vienna_constraint(start, duration=4):
        return start <= 1 and start + duration - 1 >= 4
    
    problem.addConstraint(vienna_constraint, ['Vienna_start'])
    
    # Lisbon must be between day 11 and day 13
    def lisbon_constraint(start, duration=3):
        return start <= 11 and start + duration - 1 >= 13
    
    problem.addConstraint(lisbon_constraint, ['Lisbon_start'])
    
    # Oslo must be between day 13 and day 15  
    def oslo_constraint(start, duration=3):
        return start <= 13 and start + duration - 1 >= 15
    
    problem.addConstraint(oslo_constraint, ['Oslo_start'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first solution
    solution = solutions[0]
    
    # Reconstruct the itinerary
    itinerary_data = []
    city_visits = []
    
    for city in city_names:
        start_day = solution[f'{city}_start']
        duration = cities[city]
        end_day = start_day + duration - 1
        city_visits.append({
            'city': city,
            'start': start_day,
            'end': end_day,
            'duration': duration
        })
    
    # Sort by start day
    city_visits.sort(key=lambda x: x['start'])
    
    # Create day ranges for output
    for visit in city_visits:
        if visit['start'] == visit['end']:
            day_range = f"Day {visit['start']}"
        else:
            day_range = f"Day {visit['start']}-{visit['end']}"
        
        itinerary_data.append({
            'day_range': day_range,
            'place': visit['city']
        })
    
    # Output as JSON
    result = {'itinerary': itinerary_data}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()