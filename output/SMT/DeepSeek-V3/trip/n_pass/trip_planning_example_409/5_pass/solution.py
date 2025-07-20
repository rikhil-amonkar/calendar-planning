from z3 import *

def solve_itinerary():
    # Define cities and map to integers
    cities = ['Zurich', 'Hamburg', 'Helsinki', 'Bucharest', 'Split']
    city_map = {city: idx for idx, city in enumerate(cities)}
    city_inv_map = {idx: city for idx, city in enumerate(cities)}
    
    # Create solver
    s = Solver()
    
    # Day variables (1-12)
    day_vars = [Int(f'day_{i}') for i in range(1, 13)]
    
    # Each day must be assigned to a valid city
    for day in day_vars:
        s.add(day >= 0, day < len(cities))
    
    # Direct flight connections (corrected spellings)
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Hamburg': ['Zurich', 'Bucharest', 'Helsinki', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Bucharest': ['Zurich', 'Hamburg'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    # Flight transition constraints
    for i in range(11):
        current = day_vars[i]
        next_day = day_vars[i+1]
        # Either stay or fly to connected city
        s.add(Or(
            current == next_day,
            *[And(current == city_map[city], next_day == city_map[dest]) 
              for city in direct_flights 
              for dest in direct_flights[city]]
        ))
    
    # Count days in each city
    counts = {city: 0 for city in cities}
    for city in cities:
        counts[city] = Sum([If(day_vars[i] == city_map[city], 1, 0) for i in range(12)])
    
    # Required days per city
    s.add(counts['Hamburg'] == 2)
    s.add(counts['Zurich'] == 3)
    s.add(counts['Helsinki'] == 2)
    s.add(counts['Bucharest'] == 2)
    s.add(counts['Split'] == 7)
    
    # Wedding in Zurich between day 1-3
    s.add(Or(day_vars[0] == city_map['Zurich'], 
             day_vars[1] == city_map['Zurich'], 
             day_vars[2] == city_map['Zurich']))
    
    # Conference in Split on day 4 and 10
    s.add(day_vars[3] == city_map['Split'])
    s.add(day_vars[9] == city_map['Split'])
    
    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(12):
            city_idx = model.evaluate(day_vars[i]).as_long()
            itinerary.append({"day": i+1, "place": city_inv_map[city_idx]})
        
        # Verify constraints
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            day_counts[entry['place']] += 1
        
        assert day_counts['Hamburg'] == 2
        assert day_counts['Zurich'] == 3
        assert day_counts['Helsinki'] == 2
        assert day_counts['Bucharest'] == 2
        assert day_counts['Split'] == 7
        
        zurich_days = [e['day'] for e in itinerary if e['place'] == 'Zurich']
        assert any(1 <= d <= 3 for d in zurich_days)
        
        split_days = [e['day'] for e in itinerary if e['place'] == 'Split']
        assert 4 in split_days and 10 in split_days
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(result)