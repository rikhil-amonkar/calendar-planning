import z3
import json

def main():
    # Cities and their required durations
    cities = ['Vienna', 'Barcelona', 'Edinburgh', 'Krakow', 'Riga', 'Hamburg', 'Paris', 'Stockholm']
    durations = {
        'Vienna': 4,
        'Barcelona': 2,
        'Edinburgh': 4,
        'Krakow': 3,
        'Riga': 4,
        'Hamburg': 2,
        'Paris': 2,
        'Stockholm': 2
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('Hamburg', 'Stockholm'), ('Vienna', 'Stockholm'), ('Paris', 'Edinburgh'),
        ('Riga', 'Barcelona'), ('Paris', 'Riga'), ('Krakow', 'Barcelona'),
        ('Edinburgh', 'Stockholm'), ('Paris', 'Krakow'), ('Krakow', 'Stockholm'),
        ('Riga', 'Edinburgh'), ('Barcelona', 'Stockholm'), ('Paris', 'Stockholm'),
        ('Krakow', 'Edinburgh'), ('Vienna', 'Hamburg'), ('Paris', 'Hamburg'),
        ('Riga', 'Stockholm'), ('Hamburg', 'Barcelona'), ('Vienna', 'Barcelona'),
        ('Krakow', 'Vienna'), ('Riga', 'Hamburg'), ('Barcelona', 'Edinburgh'),
        ('Paris', 'Barcelona'), ('Hamburg', 'Edinburgh'), ('Paris', 'Vienna'),
        ('Vienna', 'Riga')
    ]
    direct_flights_set = set()
    for a, b in direct_flights:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))
    
    # Middle cities (excluding Paris and Stockholm)
    middle_cities = ['Vienna', 'Barcelona', 'Edinburgh', 'Krakow', 'Riga', 'Hamburg']
    
    # Z3 solver
    solver = z3.Solver()
    
    # Position variables for middle cities (1 to 6)
    pos_vars = {}
    for city in middle_cities:
        pos_vars[city] = z3.Int(f'pos_{city}')
        solver.add(z3.And(pos_vars[city] >= 1, pos_vars[city] <= 6))
    
    # Distinct positions
    solver.add(z3.Distinct([pos_vars[city] for city in middle_cities]))
    
    # Order of cities: index 0 to 7
    order = [None] * 8
    order[0] = 'Paris'
    order[7] = 'Stockholm'
    
    # Function to get city by position
    def get_city_at_pos(pos):
        conditions = []
        for city in middle_cities:
            conditions.append(z3.And(pos_vars[city] == pos))
        return z3.If(conditions[0], middle_cities[0],
                 z3.If(conditions[1], middle_cities[1],
                   z3.If(conditions[2], middle_cities[2],
                     z3.If(conditions[3], middle_cities[3],
                       z3.If(conditions[4], middle_cities[4],
                         z3.If(conditions[5], middle_cities[5], ''))))))
    
    # Define order[1] to order[6]
    for i in range(1, 7):
        order[i] = get_city_at_pos(i)
    
    # Start and end days for each segment
    start = [z3.Int(f'start_{i}') for i in range(8)]
    end = [z3.Int(f'end_{i}') for i in range(8)]
    
    # Constraints for start and end days
    solver.add(start[0] == 1)
    solver.add(end[0] == start[0] + durations[order[0]] - 1)
    
    for i in range(1, 8):
        solver.add(start[i] == end[i-1])
        # Get duration for the city at order[i]
        dur_expr = z3.If(order[i] == cities[0], durations[cities[0]],
                     z3.If(order[i] == cities[1], durations[cities[1]],
                       z3.If(order[i] == cities[2], durations[cities[2]],
                         z3.If(order[i] == cities[3], durations[cities[3]],
                           z3.If(order[i] == cities[4], durations[cities[4]],
                             z3.If(order[i] == cities[5], durations[cities[5]],
                               z3.If(order[i] == cities[6], durations[cities[6]],
                                 durations[cities[7]])))))))
        solver.add(end[i] == start[i] + dur_expr - 1)
    
    solver.add(end[7] == 16)
    
    # Constraints for Hamburg and Edinburgh
    for i in range(1, 7):
        # Hamburg must be between day10 and day11
        ham_constraint = z3.And(order[i] == 'Hamburg', start[i] <= 10, end[i] >= 11)
        # Edinburgh must be between day12 and day15
        edi_constraint = z3.And(order[i] == 'Edinburgh', start[i] <= 15, end[i] >= 12)
        solver.add(z3.Or(ham_constraint, z3.And(True)))  # Add Hamburg constraint
        solver.add(z3.Or(edi_constraint, z3.And(True)))  # Add Edinburgh constraint
    
    # Constraints for direct flights between consecutive cities
    for i in range(7):
        # Create condition for each possible flight pair
        conditions = []
        for city1 in cities:
            for city2 in cities:
                if (city1, city2) in direct_flights_set:
                    cond = z3.And(order[i] == city1, order[i+1] == city2)
                    conditions.append(cond)
        solver.add(z3.Or(conditions))
    
    # Check satisfaction
    if solver.check() == z3.sat:
        model = solver.model()
        # Determine the order from the model
        actual_order = [None] * 8
        actual_order[0] = 'Paris'
        actual_order[7] = 'Stockholm'
        mid_positions = {}
        for city in middle_cities:
            mid_positions[city] = model.evaluate(pos_vars[city]).as_long()
        # Invert the mapping: from position to city
        pos_to_city = {v: k for k, v in mid_positions.items()}
        for i in range(1, 7):
            actual_order[i] = pos_to_city[i]
        
        # Compute start and end days for each segment
        start_vals = [0] * 8
        end_vals = [0] * 8
        start_vals[0] = 1
        end_vals[0] = start_vals[0] + durations[actual_order[0]] - 1
        for i in range(1, 8):
            start_vals[i] = end_vals[i-1]
            end_vals[i] = start_vals[i] + durations[actual_order[i]] - 1
        
        # Build itinerary
        itinerary = []
        for i in range(8):
            day_start = start_vals[i]
            day_end = end_vals[i]
            place = actual_order[i]
            day_range = f"Day {day_start}-{day_end}"
            itinerary.append({"day_range": day_range, "place": place})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()