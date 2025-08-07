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
    
    # Variables: for each day, which city we're in
    days = 15
    location = [Int(f'day_{d+1}') for d in range(days)]
    
    # Each day must be assigned to a valid city
    for d in range(days):
        s.add(location[d] >= 0, location[d] < len(cities))
    
    # Flight constraints between consecutive days
    for d in range(days - 1):
        current_city = cities[location[d]]
        next_city = cities[location[d+1]]
        # If changing cities, must be a direct flight
        s.add(Implies(location[d] != location[d+1], 
                     next_city in direct_flights[current_city]))
    
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
        total_days[city] = total
    
    s.add(total_days['Manchester'] == 7)
    s.add(total_days['Stuttgart'] == 5)
    s.add(total_days['Madrid'] == 4)
    s.add(total_days['Vienna'] == 2)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        for d in range(days):
            city_idx = model[location[d]].as_long()
            city = cities[city_idx]
            
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