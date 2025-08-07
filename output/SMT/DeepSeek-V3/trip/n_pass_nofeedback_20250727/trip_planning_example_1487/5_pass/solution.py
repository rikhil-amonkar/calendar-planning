from z3 import *

def solve_itinerary():
    # Cities to visit
    cities = ['Copenhagen', 'Geneva', 'Mykonos', 'Naples', 'Prague', 'Dubrovnik', 
              'Athens', 'Santorini', 'Brussels', 'Munich']
    
    # Required days in each city
    required_days = {
        'Copenhagen': 5,
        'Geneva': 3,
        'Mykonos': 2,
        'Naples': 4,
        'Prague': 2,
        'Dubrovnik': 3,
        'Athens': 4,
        'Santorini': 5,
        'Brussels': 4,
        'Munich': 5
    }
    
    # Direct flights between cities (bidirectional)
    direct_flights = [
        ('Copenhagen', 'Dubrovnik'), ('Brussels', 'Copenhagen'), ('Prague', 'Geneva'),
        ('Athens', 'Geneva'), ('Naples', 'Dubrovnik'), ('Athens', 'Dubrovnik'),
        ('Geneva', 'Mykonos'), ('Naples', 'Mykonos'), ('Naples', 'Copenhagen'),
        ('Munich', 'Mykonos'), ('Naples', 'Athens'), ('Prague', 'Athens'),
        ('Santorini', 'Geneva'), ('Athens', 'Santorini'), ('Naples', 'Munich'),
        ('Prague', 'Copenhagen'), ('Brussels', 'Naples'), ('Athens', 'Mykonos'),
        ('Athens', 'Copenhagen'), ('Naples', 'Geneva'), ('Dubrovnik', 'Munich'),
        ('Brussels', 'Munich'), ('Prague', 'Brussels'), ('Brussels', 'Athens'),
        ('Athens', 'Munich'), ('Geneva', 'Munich'), ('Copenhagen', 'Munich'),
        ('Brussels', 'Geneva'), ('Copenhagen', 'Geneva'), ('Prague', 'Munich'),
        ('Copenhagen', 'Santorini'), ('Naples', 'Santorini'), ('Geneva', 'Dubrovnik')
    ]
    
    # Create a dictionary of reachable cities for each city
    flight_graph = {city: set() for city in cities}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Create solver with timeout
    s = Solver()
    s.set("timeout", 30000)  # 30 second timeout
    
    # Day variables: day[i] is the city visited on day i+1 (days are 1-based)
    days = [Int(f'day_{i}') for i in range(28)]
    
    # City encodings
    city_codes = {city: idx for idx, city in enumerate(cities)}
    code_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints that each day is one of the cities
    for day in days:
        s.add(Or([day == city_codes[city] for city in cities]))
    
    # Constraints for required days per city
    for city in cities:
        count = Sum([If(day == city_codes[city], 1, 0) for day in days])
        s.add(count == required_days[city])
    
    # Hard constraints that must be satisfied
    # Conference in Mykonos on days 27-28 (0-based 26, 27)
    s.add(days[26] == city_codes['Mykonos'])
    s.add(days[27] == city_codes['Mykonos'])
    
    # Relatives in Naples between day 5-8 (0-based 4..7)
    s.add(Or([days[i] == city_codes['Naples'] for i in range(4, 8)]))
    
    # Workshop in Athens between day 8-11 (0-based 7..10)
    s.add(Or([days[i] == city_codes['Athens'] for i in range(7, 11)]))
    
    # Copenhagen between day 11 and 15 (1-based, days 10..14 in 0-based)
    s.add(Or([days[i] == city_codes['Copenhagen'] for i in range(10, 15)]))
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(27):
        current_day = days[i]
        next_day = days[i+1]
        # Create Or clause for all possible transitions
        transitions = [current_day == next_day]
        current_city_code = current_day
        next_city_code = next_day
        for city in cities:
            for neighbor in flight_graph[city]:
                transitions.append(And(current_day == city_codes[city], 
                                     next_day == city_codes[neighbor]))
        s.add(Or(transitions))
    
    # Add symmetry breaking constraints to help the solver
    # Prefer earlier visits to cities with fixed dates
    s.add(days[4] == city_codes['Naples'])  # Force Naples on day 5
    s.add(days[7] == city_codes['Athens'])   # Force Athens on day 8
    s.add(days[10] == city_codes['Copenhagen'])  # Force Copenhagen on day 11
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(28):
            city_code = model.evaluate(days[i]).as_long()
            city = code_to_city[city_code]
            itinerary.append({"day": i+1, "place": city})
        
        # Verify the solution
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Verify counts
        for city in cities:
            assert counts[city] == required_days[city], f"City {city} has {counts[city]} days instead of {required_days[city]}"
        
        # Verify special date constraints
        assert itinerary[26]['place'] == 'Mykonos' and itinerary[27]['place'] == 'Mykonos'
        assert any(5 <= entry['day'] <= 8 and entry['place'] == 'Naples' for entry in itinerary)
        assert any(8 <= entry['day'] <= 11 and entry['place'] == 'Athens' for entry in itinerary)
        assert any(11 <= entry['day'] <= 15 and entry['place'] == 'Copenhagen' for entry in itinerary)
        
        # Verify flight connections
        for i in range(27):
            current = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current != next_city:
                assert next_city in flight_graph[current], f"No flight from {current} to {next_city} on day {i+1}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run the solver
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))