from z3 import *

def solve_itinerary():
    # Cities to visit
    cities = ['Copenhagen', 'Geneva', 'Mykonos', 'Naples', 'Prague', 'Dubrovnik', 'Athens', 'Santorini', 'Brussels', 'Munich']
    
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
    
    # Direct flights between cities
    direct_flights = {
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
    }
    # Ensure flights are bidirectional
    additional_flights = set()
    for (a, b) in direct_flights:
        additional_flights.add((b, a))
    direct_flights.update(additional_flights)
    
    # Create a solver instance
    s = Solver()
    
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
    
    # Special date constraints
    # Copenhagen between day 11 and 15 (1-based, days 10..14 in 0-based)
    s.add(Or([days[i] == city_codes['Copenhagen'] for i in range(10, 15)]))
    
    # Conference in Mykonos on days 27-28 (0-based 26, 27)
    s.add(days[26] == city_codes['Mykonos'])
    s.add(days[27] == city_codes['Mykonos'])
    
    # Relatives in Naples between day 5-8 (0-based 4..7)
    s.add(Or([days[i] == city_codes['Naples'] for i in range(4, 8)]))
    
    # Workshop in Athens between day 8-11 (0-based 7..10)
    s.add(Or([days[i] == city_codes['Athens'] for i in range(7, 11)]))
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(27):
        current_day = days[i]
        next_day = days[i+1]
        s.add(Or(
            current_day == next_day,
            *[And(current_day == city_codes[a], next_day == city_codes[b]) 
              for (a, b) in direct_flights if a in city_codes and b in city_codes]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(28):
            city_code = model.evaluate(days[i]).as_long()
            city = code_to_city[city_code]
            itinerary.append({"day": i+1, "place": city})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        for city in cities:
            assert counts[city] == required_days[city], f"City {city} has {counts[city]} days instead of {required_days[city]}"
        
        # Verify the special date constraints
        copenhagen_days = [i+1 for i in range(28) if model.evaluate(days[i]).as_long() == city_codes['Copenhagen']]
        assert any(11 <= day <=15 for day in copenhagen_days), "Copenhagen not visited between day 11 and 15"
        
        assert model.evaluate(days[26]).as_long() == city_codes['Mykonos'], "Mykonos day 27 error"
        assert model.evaluate(days[27]).as_long() == city_codes['Mykonos'], "Mykonos day 28 error"
        
        naples_days = [i+1 for i in range(28) if model.evaluate(days[i]).as_long() == city_codes['Naples']]
        assert any(5 <= day <=8 for day in naples_days), "Naples not visited between day 5 and 8"
        
        athens_days = [i+1 for i in range(28) if model.evaluate(days[i]).as_long() == city_codes['Athens']]
        assert any(8 <= day <=11 for day in athens_days), "Athens not visited between day 8 and 11"
        
        # Verify flight constraints
        for i in range(27):
            current_city_code = model.evaluate(days[i]).as_long()
            next_city_code = model.evaluate(days[i+1]).as_long()
            if current_city_code != next_city_code:
                current_city = code_to_city[current_city_code]
                next_city = code_to_city[next_city_code]
                assert (current_city, next_city) in direct_flights or (next_city, current_city) in direct_flights, f"No flight between {current_city} and {next_city} on day {i+1}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run the solver
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))