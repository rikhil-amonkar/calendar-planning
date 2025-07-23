from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Brussels', 'Venice', 'London', 'Lisbon', 'Reykjavik', 'Santorini', 'Madrid']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    flights = {
        'Brussels': ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid'],
        'Venice': ['Madrid', 'Brussels', 'Santorini', 'Lisbon', 'London'],
        'London': ['Brussels', 'Madrid', 'Santorini', 'Reykjavik', 'Lisbon', 'Venice'],
        'Lisbon': ['Reykjavik', 'Venice', 'London', 'Madrid', 'Brussels'],
        'Reykjavik': ['Lisbon', 'Madrid', 'London', 'Brussels'],
        'Santorini': ['Venice', 'London', 'Madrid'],
        'Madrid': ['Venice', 'Reykjavik', 'London', 'Santorini', 'Lisbon', 'Brussels']
    }
    
    # Create Z3 variables: day[i] represents the city on day i+1 (days are 1-based)
    days = [Int(f'day_{i}') for i in range(17)]  # days 1 to 17
    
    s = Solver()
    
    # Each day must be assigned a city index (0 to 6)
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Fixed constraints:
    # Brussels on day 1 and 2
    s.add(days[0] == city_map['Brussels'])
    s.add(days[1] == city_map['Brussels'])
    
    # Venice between day 5 and 7 (inclusive)
    # So at least one of days 4,5,6 (0-based: days 5,6,7 are indices 4,5,6)
    s.add(Or([days[i] == city_map['Venice'] for i in range(4, 7)]))  # days 5-7
    
    # Madrid between day 7 and 11 (inclusive)
    # So at least one of days 6 to 10 (0-based: days 7-11 are indices 6-10)
    s.add(Or([days[i] == city_map['Madrid'] for i in range(6, 11)]))
    
    # Duration constraints:
    # Count occurrences of each city in the days list
    for city in cities:
        count = Sum([If(days[i] == city_map[city], 1, 0) for i in range(17)])
        if city == 'Brussels':
            s.add(count == 2)
        elif city == 'Venice':
            s.add(count == 3)
        elif city == 'London':
            s.add(count == 3)
        elif city == 'Lisbon':
            s.add(count == 4)
        elif city == 'Reykjavik':
            s.add(count == 3)
        elif city == 'Santorini':
            s.add(count == 3)
        elif city == 'Madrid':
            s.add(count == 5)
    
    # Flight constraints: consecutive days must be connected by a direct flight
    for i in range(16):  # days 1..16 and 2..17
        current_city = days[i]
        next_city = days[i+1]
        # For each possible current city, next city must be in its flight list
        for city in cities:
            s.add(Implies(current_city == city_map[city], Or([next_city == city_map[neighbor] for neighbor in flights[city]])))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(17):
            day_num = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Verify flight connections
        valid = True
        for i in range(16):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if next_city not in flights[current_city]:
                valid = False
                break
        
        if valid and all(counts[city] == {
            'Brussels': 2,
            'Venice': 3,
            'London': 3,
            'Lisbon': 4,
            'Reykjavik': 3,
            'Santorini': 3,
            'Madrid': 5
        }[city] for city in cities):
            return {'itinerary': itinerary}
        else:
            print("Generated itinerary does not meet constraints.")
            return None
    else:
        print("No solution found.")
        return None

# Generate and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    import json
    print(json.dumps(itinerary, indent=2))