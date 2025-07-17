from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik']
    city_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections
    direct_flights = {
        'Edinburgh': ['Berlin', 'Amsterdam', 'Brussels'],
        'Amsterdam': ['Berlin', 'Edinburgh', 'Reykjavik', 'Vienna'],
        'Berlin': ['Edinburgh', 'Amsterdam', 'Vienna', 'Brussels', 'Reykjavik'],
        'Vienna': ['Berlin', 'Reykjavik', 'Brussels', 'Amsterdam'],
        'Brussels': ['Berlin', 'Edinburgh', 'Vienna', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Amsterdam', 'Brussels', 'Berlin']
    }
    
    # Create solver
    s = Solver()
    
    # Decision variables: city for each day (1-23)
    day_city = [Int(f'day_{day}') for day in range(1, 24)]
    
    # Each day must be assigned a valid city index
    for day in range(23):
        s.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Flight constraints between consecutive days
    for day in range(22):
        current = day_city[day]
        next_day = day_city[day + 1]
        
        # Create OR of all possible direct flight connections
        flight_options = []
        for city in cities:
            for neighbor in direct_flights[city]:
                flight_options.append(And(current == city_idx[city], next_day == city_idx[neighbor]))
        s.add(Or(flight_options))
    
    # Duration constraints
    for city in cities:
        s.add(Sum([If(day_city[day] == city_idx[city], 1, 0) for day in range(23)]) == {
            'Amsterdam': 4,
            'Edinburgh': 5,
            'Brussels': 5,
            'Vienna': 5,
            'Berlin': 4,
            'Reykjavik': 5
        }[city])
    
    # Specific date range constraints
    # Amsterdam between days 5-8 (inclusive)
    s.add(Or([day_city[day] == city_idx['Amsterdam'] for day in range(4, 8)]))
    
    # Berlin between days 16-19 (inclusive)
    s.add(Or([day_city[day] == city_idx['Berlin'] for day in range(15, 19)]))
    
    # Reykjavik between days 12-16 (inclusive)
    s.add(Or([day_city[day] == city_idx['Reykjavik'] for day in range(11, 16)]))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Build the itinerary
        for day in range(23):
            city_index = m.evaluate(day_city[day]).as_long()
            itinerary.append({
                'day': day + 1,
                'city': cities[city_index]
            })
        
        # Verify all constraints are satisfied
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['city']] += 1
        
        # Check duration constraints
        assert city_days['Amsterdam'] == 4
        assert city_days['Edinburgh'] == 5
        assert city_days['Brussels'] == 5
        assert city_days['Vienna'] == 5
        assert city_days['Berlin'] == 4
        assert city_days['Reykjavik'] == 5
        
        # Check date range constraints
        assert any(5 <= entry['day'] <= 8 and entry['city'] == 'Amsterdam' for entry in itinerary)
        assert any(16 <= entry['day'] <= 19 and entry['city'] == 'Berlin' for entry in itinerary)
        assert any(12 <= entry['day'] <= 16 and entry['city'] == 'Reykjavik' for entry in itinerary)
        
        # Check flight connections
        for i in range(len(itinerary)-1):
            current = itinerary[i]['city']
            next_city = itinerary[i+1]['city']
            assert next_city in direct_flights[current]
        
        return {'itinerary': itinerary}
    else:
        print("No valid itinerary found")
        return None

# Execute and print the solution
solution = solve_itinerary()
if solution:
    print(json.dumps(solution, indent=2))