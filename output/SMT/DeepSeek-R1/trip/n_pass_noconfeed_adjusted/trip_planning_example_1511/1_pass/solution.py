from z3 import *
import json

def main():
    # Define cities and their durations
    cities = ['Venice', 'Reykjavik', 'Munich', 'Santorini', 'Manchester', 'Porto', 'Bucharest', 'Tallinn', 'Valencia', 'Vienna']
    duration = {
        'Venice': 3,
        'Reykjavik': 2,
        'Munich': 3,
        'Santorini': 3,
        'Manchester': 3,
        'Porto': 3,
        'Bucharest': 5,
        'Tallinn': 4,
        'Valencia': 2,
        'Vienna': 5
    }
    
    # Fixed start days for Munich and Valencia
    fixed_start = {
        'Munich': 4,
        'Valencia': 14
    }
    
    # Direct flights set (undirected)
    direct_flights_str = "Bucharest and Manchester, Munich and Venice, Santorini and Manchester, Vienna and Reykjavik, Venice and Santorini, Munich and Porto, Valencia and Vienna, Manchester and Vienna, Porto and Vienna, Venice and Manchester, Santorini and Vienna, Munich and Manchester, Munich and Reykjavik, Bucharest and Valencia, Venice and Vienna, Bucharest and Vienna, Porto and Manchester, Munich and Vienna, Valencia and Porto, Munich and Bucharest, Tallinn and Munich, Santorini and Bucharest, Munich and Valencia"
    direct_flights_set = set()
    for flight in direct_flights_str.split(', '):
        city1, city2 = flight.split(' and ')
        direct_flights_set.add((city1, city2))
        direct_flights_set.add((city2, city1))
    
    # Initialize solver
    s = Solver()
    
    # Create variables for start days and order
    start_day = {}
    order = {}
    for city in cities:
        if city in fixed_start:
            start_day[city] = fixed_start[city]
        else:
            start_day[city] = Int(f's_{city}')
        order[city] = Int(f'o_{city}')
    
    # Constraints for order: distinct and between 0 and 9
    s.add(Distinct([order[city] for city in cities]))
    for city in cities:
        s.add(order[city] >= 0, order[city] <= 9)
    
    # Constraint: first city (order 0) starts on day 1
    for city in cities:
        s.add(If(order[city] == 0, start_day[city] == 1, True))
    
    # Constraints for consecutive cities
    for i in cities:
        for j in cities:
            if i != j:
                # Start day constraint for consecutive cities
                cond = (order[j] == order[i] + 1)
                then_clause = (start_day[j] == start_day[i] + duration[i] - 1)
                s.add(If(cond, then_clause, True))
                
                # Direct flight constraint for consecutive cities
                if (i, j) not in direct_flights_set:
                    s.add(Not(cond))
    
    # Constraint for Santorini
    s.add(start_day['Santorini'] >= 6, start_day['Santorini'] <= 10)
    
    # Constraints for non-fixed start days
    for city in cities:
        if city not in fixed_start:
            s.add(start_day[city] >= 1)
            s.add(start_day[city] <= 24 - duration[city] + 1)
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        # Extract order and start days
        city_order = []
        for city in cities:
            o_val = m.evaluate(order[city])
            s_val = m.evaluate(start_day[city])
            if is_int_value(o_val):
                o = o_val.as_long()
            else:
                o = int(str(o_val))
            if is_int_value(s_val):
                s_val = s_val.as_long()
            else:
                s_val = int(str(s_val))
            city_order.append((o, city, s_val))
        
        city_order.sort(key=lambda x: x[0])
        itinerary = []
        for _, city, start in city_order:
            end = start + duration[city] - 1
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()