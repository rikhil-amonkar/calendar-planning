from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights as adjacency list (bidirectional)
    direct_flights = {
        'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Vienna': ['Riga', 'Reykjavik', 'Dublin'],
        'Tallinn': ['Riga', 'Dublin', 'Helsinki'],
        'Dublin': ['Riga', 'Helsinki', 'Tallinn', 'Vienna', 'Reykjavik']
    }
    
    # Z3 solver setup
    s = Solver()
    
    # Variables: day[i] is the city index (0..5) on day i+1 (since days are 1-based)
    days = [Int(f'day_{i}') for i in range(1, 16)]
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Duration constraints
    def count_city(city_idx):
        return Sum([If(day == city_idx, 1, 0) for day in days])
    
    s.add(count_city(city_map['Dublin']) == 5)
    s.add(count_city(city_map['Helsinki']) == 3)
    s.add(count_city(city_map['Riga']) == 3)
    s.add(count_city(city_map['Reykjavik']) == 2)
    s.add(count_city(city_map['Vienna']) == 2)
    s.add(count_city(city_map['Tallinn']) == 5)
    
    # Event constraints
    # Vienna: days 2 and 3 must be Vienna (annual show)
    s.add(days[1] == city_map['Vienna'])  # day 2 is index 1 (0-based)
    s.add(days[2] == city_map['Vienna'])  # day 3
    
    # Helsinki: at least one day between day 3 and day 5 (i.e., days 4,5 in 1-based)
    s.add(Or(
        days[3] == city_map['Helsinki'],  # day 4
        days[4] == city_map['Helsinki']   # day 5
    ))
    
    # Tallinn wedding between day 7 and 11 (1-based: days 6..10 in 0-based)
    s.add(Or([days[i] == city_map['Tallinn'] for i in range(6, 11)]))
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(len(days) - 1):
        current_city = days[i]
        next_city = days[i+1]
        # For each possible current city, next city must be in its direct flights
        for city in cities:
            for target_city in cities:
                if target_city not in direct_flights.get(city, []):
                    s.add(Implies(
                        current_city == city_map[city],
                        next_city != city_map[target_city]
                    ))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 16):
            city_idx = model.evaluate(days[i-1]).as_long()
            itinerary.append({"day": i, "place": cities[city_idx]})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Verify constraints
        assert counts['Dublin'] == 5
        assert counts['Helsinki'] == 3
        assert counts['Riga'] == 3
        assert counts['Reykjavik'] == 2
        assert counts['Vienna'] == 2
        assert counts['Tallinn'] == 5
        assert itinerary[1]['place'] == 'Vienna'  # day 2
        assert itinerary[2]['place'] == 'Vienna'  # day 3
        assert (itinerary[3]['place'] == 'Helsinki' or itinerary[4]['place'] == 'Helsinki')
        assert any(7 <= entry['day'] <= 11 and entry['place'] == 'Tallinn' for entry in itinerary)
        
        # Verify flights
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current != next_place:
                assert next_place in direct_flights[current], f"No direct flight from {current} to {next_place} on day {i+1}"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))