from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights adjacency list
    direct_flights = {
        'Vienna': ['Stuttgart', 'Manchester', 'Madrid'],
        'Stuttgart': ['Vienna', 'Manchester'],
        'Manchester': ['Vienna', 'Stuttgart', 'Madrid'],
        'Madrid': ['Vienna', 'Manchester']
    }
    
    s = Solver()
    
    # Variables: for each day, start and end city
    days = 15
    start_city = [Int(f'start_{d+1}') for d in range(days)]
    end_city = [Int(f'end_{d+1}') for d in range(days)]
    
    # Constraints for each day's start and end cities
    for d in range(days):
        s.add(start_city[d] >= 0, start_city[d] < len(cities))
        s.add(end_city[d] >= 0, end_city[d] < len(cities))
        # If start != end, there must be a direct flight
        for c1 in range(len(cities)):
            for c2 in range(len(cities)):
                if c1 != c2:
                    city1 = cities[c1]
                    city2 = cities[c2]
                    if city2 not in direct_flights[city1]:
                        s.add(Not(And(start_city[d] == c1, end_city[d] == c2)))
    
    # Manchester must be visited from day 1 to 7 (wedding)
    for d in range(7):
        s.add(Or(start_city[d] == city_to_idx['Manchester'], end_city[d] == city_to_idx['Manchester']))
    
    # Stuttgart must be visited between day 11-15 (workshop)
    for d in range(10, 15):  # days 11-15 (1-based)
        s.add(Or(start_city[d] == city_to_idx['Stuttgart'], end_city[d] == city_to_idx['Stuttgart']))
    
    # Continuity constraints: end city of day d is start city of day d+1
    for d in range(days - 1):
        s.add(end_city[d] == start_city[d + 1])
    
    # Total days per city constraints
    total_days = {city: 0 for city in cities}
    for city in cities:
        idx = city_to_idx[city]
        total = 0
        for d in range(days):
            total += If(Or(start_city[d] == idx, end_city[d] == idx), 1, 0)
        s.add(total == {'Manchester':7, 'Stuttgart':5, 'Madrid':4, 'Vienna':2}[city])
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in range(days):
            day_num = d + 1
            start = model[start_city[d]].as_long()
            end = model[end_city[d]].as_long()
            start_city_name = cities[start]
            end_city_name = cities[end]
            if start == end:
                itinerary.append({'day': day_num, 'place': start_city_name})
            else:
                itinerary.append({'day': day_num, 'place': f"{start_city_name}->{end_city_name}"})
        
        # Verify counts
        counts = {city:0 for city in cities}
        for entry in itinerary:
            places = entry['place'].split('->')
            for place in places:
                counts[place] += 1
        assert counts['Manchester'] == 7
        assert counts['Stuttgart'] == 5
        assert counts['Madrid'] == 4
        assert counts['Vienna'] == 2
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No solution found"}

itinerary = solve_itinerary()
print(itinerary)