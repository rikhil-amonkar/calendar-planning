from z3 import *
import json

def main():
    # Cities and their required days
    cities = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Venice', 'Amsterdam', 'Nice', 'Barcelona', 'Porto']
    days_required = [3, 5, 2, 5, 5, 4, 2, 2, 4]
    
    # Mapping city names to indices
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights data
    flights_str = """
    Venice and Nice, Naples and Amsterdam, Barcelona and Nice, Amsterdam and Nice, Stuttgart and Valencia, Stuttgart and Porto, Split and Stuttgart, Split and Naples, Valencia and Amsterdam, Barcelona and Porto, Valencia and Naples, Venice and Amsterdam, Barcelona and Naples, Barcelona and Valencia, Split and Amsterdam, Barcelona and Venice, Stuttgart and Amsterdam, Naples and Nice, Venice and Stuttgart, Split and Barcelona, Porto and Nice, Barcelona and Stuttgart, Venice and Naples, Porto and Amsterdam, Porto and Valencia, Stuttgart and Naples, Barcelona and Amsterdam.
    """
    
    # Parse flight connections
    allowed_edges = set()
    pairs = flights_str.strip().split(',')
    for p in pairs:
        p = p.strip().rstrip('.')
        if ' and ' in p:
            city1, city2 = p.split(' and ')
            city1 = city1.strip()
            city2 = city2.strip()
            if city1 in city_index and city2 in city_index:
                idx1 = city_index[city1]
                idx2 = city_index[city2]
                allowed_edges.add((idx1, idx2))
                allowed_edges.add((idx2, idx1))
    
    # Create solver
    s = Solver()
    
    # Variables for start and end days of each city
    starts = [Int(f'start_{city}') for city in cities]
    ends = [Int(f'end_{city}') for city in cities]
    
    # Order of cities (permutation)
    order = [Int(f'order_{i}') for i in range(9)]
    
    # Constraints for order: distinct and between 0 and 8
    s.add(Distinct(order))
    for i in range(9):
        s.add(And(order[i] >= 0, order[i] < 9))
    
    # Constraints for start and end days
    for i in range(9):
        s.add(And(starts[i] >= 1, starts[i] <= 24))
        s.add(And(ends[i] >= 1, ends[i] <= 24))
        s.add(ends[i] - starts[i] + 1 == days_required[i])
    
    # Specific constraints
    # Naples: 3 days, and between day 18-20
    naples_idx = city_index['Naples']
    s.add(And(starts[naples_idx] <= 20, ends[naples_idx] >= 18))
    
    # Venice: 5 days, conference day 6-10
    venice_idx = city_index['Venice']
    s.add(starts[venice_idx] <= 6)
    s.add(ends[venice_idx] >= 10)
    
    # Barcelona: 2 days, workshop day 5-6
    barcelona_idx = city_index['Barcelona']
    s.add(starts[barcelona_idx] <= 5)
    s.add(ends[barcelona_idx] >= 6)
    
    # Nice: 2 days, meet friends day 23-24
    nice_idx = city_index['Nice']
    s.add(starts[nice_idx] <= 23)
    s.add(ends[nice_idx] >= 24)
    
    # Constraints for order and flights
    s.add(ends[order[0]] == 24)  # Last city ends at day 24
    s.add(starts[order[8]] == 1)  # First city starts at day 1
    for i in range(8):
        # Consecutive cities share a travel day
        s.add(ends[order[i]] == starts[order[i+1]])
        # Direct flight required between consecutive cities
        s.add((order[i], order[i+1]) in allowed_edges)
    
    # Check feasibility
    if s.check() == sat:
        m = s.model()
        # Extract the order of cities
        visit_order = []
        for i in range(9):
            visit_order.append(m.evaluate(order[i]).as_long())
        
        # Extract start and end days for each city
        city_starts = [m.evaluate(starts[i]).as_long() for i in range(9)]
        city_ends = [m.evaluate(ends[i]).as_long() for i in range(9)]
        
        # Create itinerary in order of visit
        itinerary = []
        for idx in visit_order:
            city = cities[idx]
            start_day = city_starts[idx]
            end_day = city_ends[idx]
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()