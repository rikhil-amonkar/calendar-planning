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
    
    # Create variables for start day of each city visit
    city_names = list(cities.keys())
    
    # Add variables for order (1-7) and start day (1-15)
    for city in city_names:
        problem.addVariable(f'{city}_order', range(1, 8))
        # Start day must allow for the full duration within 15 days
        problem.addVariable(f'{city}_start', range(1, 16))
    
    # All cities must have different orders
    problem.addConstraint(AllDifferentConstraint(), [f'{city}_order' for city in city_names])
    
    # No overlap constraint - ensure visits don't overlap
    for i, city1 in enumerate(city_names):
        for city2 in city_names[i+1:]:
            def no_overlap(start1, start2, dur1=cities[city1], dur2=cities[city2]):
                return (start1 + dur1 <= start2) or (start2 + dur2 <= start1)
            
            problem.addConstraint(no_overlap, [f'{city1}_start', f'{city2}_start'])
    
    # Flight connectivity constraint - improved approach
    def flight_connectivity(orders):
        # Create mapping from order to city
        order_to_city = {}
        for i, city in enumerate(city_names):
            order_to_city[orders[i]] = city
        
        # Check consecutive cities in sequence
        sorted_orders = sorted(orders)
        for i in range(len(sorted_orders) - 1):
            city1 = order_to_city[sorted_orders[i]]
            city2 = order_to_city[sorted_orders[i + 1]]
            
            if city2 not in direct_flights[city1]:
                return False
        
        return True
    
    # Add flight connectivity constraint (only on orders)
    problem.addConstraint(flight_connectivity, [f'{city}_order' for city in city_names])
    
    # Special date constraints - made more flexible
    
    # Vienna: conference on day 1 and day 4
    # Vienna must include both day 1 and day 4
    def vienna_constraint(start, duration=4):
        end = start + duration - 1
        return start <= 1 and end >= 4
    
    problem.addConstraint(vienna_constraint, ['Vienna_start'])
    
    # Lisbon: relatives between day 11 and day 13
    # Lisbon visit must overlap with days 11-13
    def lisbon_constraint(start, duration=3):
        end = start + duration - 1
        return (start <= 13 and end >= 11)  # Overlap with 11-13
    
    problem.addConstraint(lisbon_constraint, ['Lisbon_start'])
    
    # Oslo: friend between day 13 and day 15
    # Oslo visit must overlap with days 13-15
    def oslo_constraint(start, duration=3):
        end = start + duration - 1
        return (start <= 15 and end >= 13)  # Overlap with 13-15
    
    problem.addConstraint(oslo_constraint, ['Oslo_start'])
    
    # Additional constraint: all visits must end by day 15
    for city in city_names:
        def end_by_day_15(start, duration=cities[city]):
            return start + duration - 1 <= 15
        problem.addConstraint(end_by_day_15, [f'{city}_start'])
    
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
            'duration': duration,
            'order': solution[f'{city}_order']
        })
    
    # Sort by order to show the travel sequence
    city_visits.sort(key=lambda x: x['order'])
    
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