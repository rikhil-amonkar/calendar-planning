from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (undirected)
    direct_flights = [
        ('Porto', 'Amsterdam'),
        ('Munich', 'Amsterdam'),
        ('Reykjavik', 'Amsterdam'),
        ('Munich', 'Porto'),
        ('Prague', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Amsterdam', 'Santorini'),
        ('Prague', 'Amsterdam'),
        ('Prague', 'Munich')
    ]
    
    # Create a adjacency list for direct flights
    adjacency = {i: set() for i in range(len(cities))}
    for a, b in direct_flights:
        i = city_to_idx[a]
        j = city_to_idx[b]
        adjacency[i].add(j)
        adjacency[j].add(i)
    
    # Z3 variables: day 1..16, each is a city index (0..5)
    days = 16
    X = [Int(f'X_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day is a city index
    for x in X:
        s.add(And(x >= 0, x < len(cities)))
    
    # Flight transitions: consecutive days must be same city or adjacent
    for i in range(days - 1):
        current = X[i]
        next_ = X[i + 1]
        s.add(Or(current == next_, 
                 Or([next_ == j for j in adjacency[current.as_long() if current.is_int()]])))
    
    # Total days per city
    required_days = {
        'Porto': 5,
        'Prague': 4,
        'Reykjavik': 4,
        'Santorini': 2,
        'Amsterdam': 2,
        'Munich': 4
    }
    
    for city, days_req in required_days.items():
        city_idx = city_to_idx[city]
        s.add(Sum([If(X[i] == city_idx, 1, 0) for i in range(days)]) == days_req)
    
    # Specific constraints:
    # Porto: 5 days (anywhere)
    # Prague: 4 days
    # Reykjavik: 4 days, wedding between day 4 and 7 (so must be in Reykjavik on at least one of days 4,5,6,7)
    s.add(Or([X[i] == city_to_idx['Reykjavik'] for i in range(3, 7)]))  # days 4-7 (indices 3-6)
    
    # Santorini: 2 days
    # Amsterdam: 2 days, conference on day 14 and 15 (must be in Amsterdam on those days)
    s.add(X[13] == city_to_idx['Amsterdam'])  # day 14 is index 13
    s.add(X[14] == city_to_idx['Amsterdam'])  # day 15 is index 14
    
    # Munich: 4 days, meet friend between day 7 and 10 (must be in Munich on at least one of days 7-10)
    s.add(Or([X[i] == city_to_idx['Munich'] for i in range(6, 10)]))  # days 7-10 (indices 6-9)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
        for day in range(1, days + 1):
            city_idx = m.evaluate(X[day - 1]).as_long()
            itinerary.append({'day': day, 'place': city_names[city_idx]})
        
        # Verify the solution meets all constraints
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        assert counts['Porto'] == 5
        assert counts['Prague'] == 4
        assert counts['Reykjavik'] == 4
        assert counts['Santorini'] == 2
        assert counts['Amsterdam'] == 2
        assert counts['Munich'] == 4
        
        # Check specific constraints
        wedding_days = [entry for entry in itinerary if entry['day'] in [4,5,6,7] and entry['place'] == 'Reykjavik']
        assert len(wedding_days) >= 1
        
        assert itinerary[13]['place'] == 'Amsterdam'
        assert itinerary[14]['place'] == 'Amsterdam'
        
        friend_days = [entry for entry in itinerary if entry['day'] in [7,8,9,10] and entry['place'] == 'Munich']
        assert len(friend_days) >= 1
        
        for i in range(len(itinerary) - 1):
            current = itinerary[i]['place']
            next_ = itinerary[i + 1]['place']
            if current != next_:
                assert (current, next_) in direct_flights or (next_, current) in direct_flights
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")