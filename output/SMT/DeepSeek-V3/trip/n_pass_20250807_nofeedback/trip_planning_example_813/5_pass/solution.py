from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections
    direct_flights = {
        'Frankfurt': ['Dublin', 'London', 'Vilnius', 'Stuttgart'],
        'Dublin': ['Frankfurt', 'London', 'Seville', 'Santorini'],
        'London': ['Frankfurt', 'Dublin', 'Santorini', 'Stuttgart'],
        'Vilnius': ['Frankfurt'],
        'Stuttgart': ['Frankfurt', 'London'],
        'Seville': ['Dublin'],
        'Santorini': ['London', 'Dublin']
    }
    
    # Required days in each city
    required_days = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }
    
    # Create Z3 variables for each day (1-17)
    num_days = 17
    day = [Int(f'day_{i}') for i in range(num_days)]
    
    s = Solver()
    
    # Each day must be a valid city index
    for d in day:
        s.add(And(d >= 0, d <= 6))
    
    # Count days in each city (including flight days)
    for city, idx in city_to_idx.items():
        count = Sum([If(d == idx, 1, 0) for d in day])
        s.add(count == required_days[city])
    
    # Flight constraints between consecutive days
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Either stay in same city or fly to connected city
        s.add(Or(
            current_city == next_city,
            And(current_city != next_city,
                Or([And(current_city == city_to_idx[city],
                    next_city == city_to_idx[adj_city])
                   for city in direct_flights
                   for adj_city in direct_flights[city]]))
        ))
    
    # Special constraints
    # London must be visited on day 9 or 10
    s.add(Or(day[8] == city_to_idx['London'], day[9] == city_to_idx['London']))
    
    # Stuttgart must be visited on day 7, 8, or 9
    s.add(Or(day[6] == city_to_idx['Stuttgart'],
             day[7] == city_to_idx['Stuttgart'],
             day[8] == city_to_idx['Stuttgart']))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(num_days):
            day_num = i + 1
            city_idx = model.evaluate(day[i]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the solution meets all constraints
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        for city in cities:
            assert counts[city] == required_days[city], f"City {city} has wrong day count"
        
        for i in range(num_days - 1):
            current = itinerary[i]['place']
            next = itinerary[i + 1]['place']
            if current != next:
                assert next in direct_flights[current], f"No flight from {current} to {next}"
        
        london_days = [e['day'] for e in itinerary if e['place'] == 'London']
        assert any(9 <= d <= 10 for d in london_days), "London not visited on days 9-10"
        
        stuttgart_days = [e['day'] for e in itinerary if e['place'] == 'Stuttgart']
        assert any(7 <= d <= 9 for d in stuttgart_days), "Stuttgart not visited on days 7-9"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))