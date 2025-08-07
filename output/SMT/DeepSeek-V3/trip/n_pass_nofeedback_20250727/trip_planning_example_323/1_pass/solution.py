from z3 import *

def solve_itinerary():
    # Cities
    cities = ['London', 'Oslo', 'Split', 'Porto']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections (undirected)
    connections = [
        ('London', 'Oslo'),
        ('Split', 'Oslo'),
        ('Oslo', 'Porto'),
        ('London', 'Split')
    ]
    
    # Create a connection set for quick lookup
    connected = set()
    for a, b in connections:
        connected.add((a, b))
        connected.add((b, a))
    
    # Days are 1..16
    days = 16
    
    # Z3 variables: each day is assigned to a city
    assignments = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day's assignment must be 0..3 (representing the cities)
    for day in assignments:
        s.add(day >= 0, day < len(cities))
    
    # Function to check if a transition between two cities is allowed
    def is_connected(city1, city2):
        return (cities[city1], cities[city2]) in connected
    
    # Constraints for transitions between consecutive days
    for i in range(days - 1):
        current_city = assignments[i]
        next_city = assignments[i + 1]
        # If city changes, ensure there's a direct flight
        s.add(If(current_city != next_city, 
                 is_connected(current_city, next_city), 
                 True))
    
    # Constraints for each city's stay
    # Split: 5 days, including days 7-11 (days 7 to 11 are 1-based, indices 6..10)
    split_idx = city_map['Split']
    s.add(sum([If(assignments[i] == split_idx, 1, 0) for i in range(6, 11)]) == 5)  # days 7-11 must be Split
    # Wait, the problem says "from day 7 to day 11, there's a show in Split. So days 7,8,9,10,11 (5 days) must be in Split.
    for i in range(6, 11):  # 1-based days 7-11 → 0-based indices 6-10
        s.add(assignments[i] == split_idx)
    # Total Split days is 5 (already covered)
    
    # London: 7 days, with some between day 1 and day 7 (1-based days 1..7 → 0-based 0..6)
    london_idx = city_map['London']
    s.add(sum([If(assignments[i] == london_idx, 1, 0) for i in range(0, 7)]) >= 1)  # at least one day in London in days 1-7
    s.add(sum([If(assignments[i] == london_idx, 1, 0) for i in range(days)]) == 7)
    
    # Oslo: 2 days
    oslo_idx = city_map['Oslo']
    s.add(sum([If(assignments[i] == oslo_idx, 1, 0) for i in range(days)]) == 2)
    
    # Porto: 5 days
    porto_idx = city_map['Porto']
    s.add(sum([If(assignments[i] == porto_idx, 1, 0) for i in range(days)]) == 5)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_idx = m.evaluate(assignments[i]).as_long()
            itinerary.append({'day': i + 1, 'city': cities[city_idx]})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['city']] += 1
        assert counts['Split'] == 5
        assert counts['Oslo'] == 2
        assert counts['London'] == 7
        assert counts['Porto'] == 5
        
        # Verify days 7-11 are Split
        for day in range(7, 12):
            assert itinerary[day - 1]['city'] == 'Split'
        
        # Verify at least one day in London in days 1-7
        london_in_first_7 = any(entry['city'] == 'London' for entry in itinerary[:7])
        assert london_in_first_7
        
        # Verify transitions are valid
        for i in range(days - 1):
            current_city = itinerary[i]['city']
            next_city = itinerary[i + 1]['city']
            if current_city != next_city:
                assert (current_city, next_city) in connected
        
        # Prepare the output
        output = {
            'itinerary': [
                {'day': entry['day'], 'city': entry['city']} for entry in itinerary
            ]
        }
        return output
    else:
        return None

# Solve and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    import json
    print(json.dumps(itinerary, indent=2))
else:
    print("No valid itinerary found.")