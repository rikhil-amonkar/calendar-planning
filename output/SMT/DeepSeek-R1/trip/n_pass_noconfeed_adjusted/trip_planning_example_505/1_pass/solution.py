from z3 import *
import json

def main():
    # Cities encoding: Prague=0, Stuttgart=1, Split=2, Krakow=3, Florence=4
    cities = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
    n_days = 8
    n_cities = len(cities)
    
    # Direct flights (unordered pairs)
    direct_flights = set()
    flights = [(1,2), (0,4), (3,1), (3,2), (2,0), (3,0)]
    for (a, b) in flights:
        direct_flights.add((min(a, b), max(a, b)))
    
    solver = Solver()
    
    # sleep_city[d] = city index where we sleep on day d (0-indexed days 1..8)
    sleep_city = [Int('sleep_city_%d' % d) for d in range(1, n_days+1)]
    for d in range(n_days):
        solver.add(sleep_city[d] >= 0, sleep_city[d] < n_cities)
    
    # in_city[d][c] is True if we are in city c on day d+1
    in_city = [[Bool('in_city_%d_%d' % (d+1, c)) for c in range(n_cities)] for d in range(n_days)]
    
    # Constraints for in_city: 
    # Day 1: only the sleep city
    for c in range(n_cities):
        solver.add(in_city[0][c] == (sleep_city[0] == c))
    
    # Days 2-8: current sleep city or previous sleep city if traveled
    for d in range(1, n_days):
        for c in range(n_cities):
            # We are in city c on day d+1 if:
            # - We sleep there that night (sleep_city[d] == c), OR
            # - We slept there previous night (sleep_city[d-1] == c) and today we sleep elsewhere (travel day)
            solver.add(in_city[d][c] == Or(
                sleep_city[d] == c,
                And(sleep_city[d-1] == c, sleep_city[d] != sleep_city[d-1])
            ))
    
    # Total days per city constraints
    total_days = [0]*n_cities
    for c in range(n_cities):
        total_days[c] = Sum([If(in_city[d][c], 1, 0) for d in range(n_days)])
    solver.add(total_days[0] == 4)  # Prague
    solver.add(total_days[1] == 2)  # Stuttgart
    solver.add(total_days[2] == 2)  # Split
    solver.add(total_days[3] == 2)  # Krakow
    solver.add(total_days[4] == 2)  # Florence
    
    # Specific day constraints
    # Wedding in Stuttgart between day 2 and day 3 -> must be in Stuttgart on day 3
    solver.add(in_city[2][1] == True)  # Day 3 is index 2 (0-indexed)
    # Meet friends in Split between day 3 and day 4 -> must be in Split on day 4
    solver.add(in_city[3][2] == True)  # Day 4 is index 3
    
    # Direct flight constraints between consecutive sleep cities
    for d in range(1, n_days):
        prev_city = sleep_city[d-1]
        curr_city = sleep_city[d]
        # If different cities, must have direct flight
        flight_pair = If(prev_city < curr_city, (prev_city, curr_city), (curr_city, prev_city))
        solver.add(Implies(prev_city != curr_city, 
                           Or([And(flight_pair[0] == a, flight_pair[1] == b) for (a,b) in direct_flights])))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        sleep_assignments = []
        for d in range(n_days):
            city_idx = model.evaluate(sleep_city[d]).as_long()
            sleep_assignments.append(cities[city_idx])
        
        # Generate itinerary with consecutive day ranges
        itinerary = []
        current_city = sleep_assignments[0]
        start_day = 1
        for day in range(1, n_days):
            if sleep_assignments[day] != current_city:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": current_city
                })
                current_city = sleep_assignments[day]
                start_day = day + 1
        itinerary.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": current_city
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()