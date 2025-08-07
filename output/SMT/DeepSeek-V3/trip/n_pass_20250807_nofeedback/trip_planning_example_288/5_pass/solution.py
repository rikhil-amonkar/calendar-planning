from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    city_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights between cities
    direct_flights = {
        'Vienna': ['Stuttgart', 'Manchester', 'Madrid'],
        'Stuttgart': ['Vienna', 'Manchester'],
        'Manchester': ['Vienna', 'Stuttgart', 'Madrid'],
        'Madrid': ['Vienna', 'Manchester']
    }
    
    s = Solver()
    
    # Variables: for each day, which city we're in (0-3)
    days = 15
    location = [Int(f'day_{d+1}') for d in range(days)]
    
    # Each day must be assigned to a valid city index
    for d in range(days):
        s.add(location[d] >= 0, location[d] < len(cities))
    
    # Flight constraints between consecutive days
    for d in range(days - 1):
        current = location[d]
        next_ = location[d+1]
        # Create constraints for each possible city transition
        for c1 in range(len(cities)):
            for c2 in range(len(cities)):
                if c1 != c2:
                    city1 = cities[c1]
                    city2 = cities[c2]
                    if city2 not in direct_flights[city1]:
                        s.add(Not(And(current == c1, next_ == c2)))
    
    # Manchester must be visited from day 1 to 7 (wedding)
    for d in range(7):
        s.add(location[d] == city_idx['Manchester'])
    
    # Stuttgart must be visited between day 11-15 (workshop)
    for d in range(10, 15):
        s.add(location[d] == city_idx['Stuttgart'])
    
    # Total days per city constraints
    total_days = {city: 0 for city in cities}
    for city in cities:
        idx = city_idx[city]
        total = 0
        for d in range(days):
            total += If(location[d] == idx, 1, 0)
        s.add(total == {'Manchester': 7, 'Stuttgart': 5, 'Madrid': 4, 'Vienna': 2}[city])
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        for d in range(days):
            city_idx_val = model[location[d]].as_long()
            city = cities[city_idx_val]
            
            if city != current_place:
                if current_place is not None:
                    itinerary.append({
                        'day_range': f'Day {start_day}-{d}',
                        'place': current_place
                    })
                current_place = city
                start_day = d + 1
        
        # Add the last stay
        itinerary.append({
            'day_range': f'Day {start_day}-{days}',
            'place': current_place
        })
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            days_in_place = int(entry['day_range'].split('-')[1]) - int(entry['day_range'].split('-')[0][4:]) + 1
            counts[entry['place']] += days_in_place
        
        assert counts['Manchester'] == 7
        assert counts['Stuttgart'] == 5
        assert counts['Madrid'] == 4
        assert counts['Vienna'] == 2
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No solution found"}

itinerary = solve_itinerary()
print(itinerary)