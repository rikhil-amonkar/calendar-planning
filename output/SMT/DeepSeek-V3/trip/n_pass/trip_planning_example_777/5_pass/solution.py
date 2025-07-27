from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = {
        'Dublin': ['Helsinki', 'Riga', 'Tallinn', 'Vienna', 'Reykjavik'],
        'Helsinki': ['Dublin', 'Riga', 'Tallinn', 'Reykjavik'],
        'Riga': ['Dublin', 'Helsinki', 'Tallinn', 'Vienna'],
        'Reykjavik': ['Dublin', 'Helsinki', 'Vienna'],
        'Vienna': ['Dublin', 'Riga', 'Reykjavik'],
        'Tallinn': ['Dublin', 'Helsinki', 'Riga']
    }
    
    # Create solver
    s = Solver()
    
    # Decision variables: city for each day (1-15)
    day_city = [Int(f'day_{i}') for i in range(1, 16)]
    for dc in day_city:
        s.add(dc >= 0, dc < len(cities))
    
    # Duration constraints
    def days_in_city(city):
        return Sum([If(day_city[i] == city_idx[city], 1, 0) for i in range(15)])
    
    s.add(days_in_city('Dublin') == 5)
    s.add(days_in_city('Helsinki') == 3)
    s.add(days_in_city('Riga') == 3)
    s.add(days_in_city('Reykjavik') == 2)
    s.add(days_in_city('Vienna') == 2)
    s.add(days_in_city('Tallinn') == 5)
    
    # Event constraints
    # Vienna must be days 2 and 3 (indices 1 and 2)
    s.add(day_city[1] == city_idx['Vienna'])
    s.add(day_city[2] == city_idx['Vienna'])
    
    # Helsinki must include day 4 or 5 (indices 3 or 4)
    s.add(Or(day_city[3] == city_idx['Helsinki'], 
             day_city[4] == city_idx['Helsinki']))
    
    # Tallinn must include at least one day between 7-11 (indices 6-10)
    s.add(Or([day_city[i] == city_idx['Tallinn'] for i in range(6, 11)]))
    
    # Flight constraints
    for i in range(14):  # Compare day i and i+1
        current = day_city[i]
        next_day = day_city[i+1]
        # Allow staying in same city
        same_city = (current == next_day)
        # Or moving to connected city
        valid_flight = Or([And(current == city_idx[city], 
                              next_day == city_idx[dest])
                         for city in cities 
                         for dest in direct_flights[city]])
        s.add(Or(same_city, valid_flight))
    
    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 16):
            city_index = model.evaluate(day_city[day-1]).as_long()
            itinerary.append({"day": day, "place": cities[city_index]})
        
        # Verify all constraints
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        assert counts['Dublin'] == 5
        assert counts['Helsinki'] == 3
        assert counts['Riga'] == 3
        assert counts['Reykjavik'] == 2
        assert counts['Vienna'] == 2
        assert counts['Tallinn'] == 5
        assert itinerary[1]['place'] == 'Vienna'  # day 2
        assert itinerary[2]['place'] == 'Vienna'  # day 3
        assert (itinerary[3]['place'] == 'Helsinki' or 
                itinerary[4]['place'] == 'Helsinki')
        assert any(7 <= entry['day'] <= 11 and entry['place'] == 'Tallinn' 
                  for entry in itinerary)
        
        # Verify flights
        for i in range(len(itinerary)-1):
            current = itinerary[i]['place']
            next_p = itinerary[i+1]['place']
            if current != next_p:
                assert next_p in direct_flights[current], \
                    f"Invalid flight from {current} to {next_p} on day {i+1}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))