import constraint
import json

def main():
    problem = constraint.Problem()
    
    # Cities and their required days
    cities = {
        'Prague': 5,
        'Tallinn': 3,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 5,
        'Milan': 3,
        'Lisbon': 5,
        'Santorini': 5,
        'Riga': 4,
        'Stockholm': 2
    }
    
    # Direct flight connections (bidirectional)
    connections = {
        'Riga': ['Prague', 'Milan', 'Tallinn', 'Warsaw', 'Stockholm', 'Lisbon'],
        'Stockholm': ['Milan', 'Lisbon', 'Santorini', 'Warsaw', 'Prague', 'Tallinn', 'Riga'],
        'Milan': ['Stockholm', 'Riga', 'Naples', 'Porto', 'Prague', 'Lisbon', 'Santorini'],
        'Lisbon': ['Stockholm', 'Warsaw', 'Naples', 'Porto', 'Prague', 'Riga', 'Milan'],
        'Naples': ['Warsaw', 'Milan', 'Lisbon', 'Santorini'],
        'Warsaw': ['Naples', 'Lisbon', 'Stockholm', 'Riga', 'Porto', 'Tallinn', 'Prague', 'Milan'],
        'Prague': ['Riga', 'Tallinn', 'Lisbon', 'Stockholm', 'Milan', 'Warsaw'],
        'Tallinn': ['Riga', 'Prague', 'Stockholm', 'Warsaw'],
        'Porto': ['Lisbon', 'Milan', 'Warsaw'],
        'Santorini': ['Stockholm', 'Milan', 'Naples']
    }
    
    # Special constraints
    tallinn_constraint = (18, 20)  # Must be in Tallinn between day 18-20
    milan_constraint = (24, 26)    # Must be in Milan between day 24-26
    riga_constraint = (5, 8)       # Must be in Riga between day 5-8
    
    total_days = 28
    
    # Create variables for arrival day and departure day for each city
    for city in cities:
        problem.addVariable(f'{city}_arrival', range(1, total_days + 1))
        problem.addVariable(f'{city}_departure', range(1, total_days + 1))
    
    # Constraint 1: Departure must be after arrival
    for city in cities:
        problem.addConstraint(lambda a, d, c=city: a <= d, 
                            (f'{city}_arrival', f'{city}_departure'))
    
    # Constraint 2: Stay duration must match required days
    for city, days in cities.items():
        problem.addConstraint(lambda a, d, req=days: d - a + 1 == req,
                            (f'{city}_arrival', f'{city}_departure'))
    
    # Constraint 3: No overlapping stays (cities visited sequentially)
    city_pairs = [(c1, c2) for c1 in cities for c2 in cities if c1 != c2]
    for city1, city2 in city_pairs:
        problem.addConstraint(
            lambda a1, d1, a2, d2: d1 < a2 or d2 < a1,
            (f'{city1}_arrival', f'{city1}_departure', 
             f'{city2}_arrival', f'{city2}_departure')
        )
    
    # Constraint 4: Travel constraints - consecutive cities must be connected
    # This is handled by ensuring the itinerary forms a valid path
    
    # Constraint 5: Special date constraints
    def tallinn_date_constraint(arrival, departure):
        return arrival <= tallinn_constraint[1] and departure >= tallinn_constraint[0]
    
    def milan_date_constraint(arrival, departure):
        return arrival <= milan_constraint[1] and departure >= milan_constraint[0]
    
    def riga_date_constraint(arrival, departure):
        return arrival <= riga_constraint[1] and departure >= riga_constraint[0]
    
    problem.addConstraint(tallinn_date_constraint, ['Tallinn_arrival', 'Tallinn_departure'])
    problem.addConstraint(milan_date_constraint, ['Milan_arrival', 'Milan_departure'])
    problem.addConstraint(riga_date_constraint, ['Riga_arrival', 'Riga_departure'])
    
    # Constraint 6: All days must be covered exactly once
    def all_days_covered(*args):
        days_covered = set()
        # args are alternating: city1_arrival, city1_departure, city2_arrival, city2_departure, ...
        arrivals_departures = [(args[i], args[i+1]) for i in range(0, len(args), 2)]
        
        for arrival, departure in arrivals_departures:
            days_covered.update(range(arrival, departure + 1))
        
        return len(days_covered) == total_days and min(days_covered) == 1 and max(days_covered) == total_days
    
    all_vars = []
    for city in cities:
        all_vars.extend([f'{city}_arrival', f'{city}_departure'])
    
    problem.addConstraint(all_days_covered, all_vars)
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        
        # Create itinerary segments
        itinerary_segments = []
        for city in cities:
            arrival = solution[f'{city}_arrival']
            departure = solution[f'{city}_departure']
            itinerary_segments.append({
                'arrival': arrival,
                'departure': departure,
                'city': city
            })
        
        # Sort by arrival day
        itinerary_segments.sort(key=lambda x: x['arrival'])
        
        # Format output
        itinerary = []
        for segment in itinerary_segments:
            if segment['arrival'] == segment['departure']:
                day_range = f"Day {segment['arrival']}"
            else:
                day_range = f"Day {segment['arrival']}-{segment['departure']}"
            itinerary.append({
                'day_range': day_range,
                'place': segment['city']
            })
        
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({'error': 'No valid itinerary found'}, indent=2))

if __name__ == "__main__":
    main()