from z3 import *
import json

def main():
    # Cities and their indices
    cities = ['London', 'Oslo', 'Split', 'Porto']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (undirected)
    direct_flights = [('London', 'Oslo'), ('Split', 'Oslo'), ('Oslo', 'Porto'), ('London', 'Split')]
    direct_set = set()
    for a, b in direct_flights:
        direct_set.add((a, b))
        direct_set.add((b, a))
    
    # Required days per city
    req_days = {
        'London': 7,
        'Oslo': 2,
        'Split': 5,
        'Porto': 5
    }
    
    # Z3 solver
    solver = Solver()
    
    # 16 days, 4 cities: in_city[day][city] is True if we are in the city on that day
    in_city = [[Bool(f"day_{day+1}_{city}") for city in cities] for day in range(16)]
    
    # Constraint: Each day must be in at least one city and at most two cities
    for day in range(16):
        city_flags = [in_city[day][idx] for idx in range(4)]
        solver.add(AtLeast(*city_flags, 1))
        solver.add(AtMost(*city_flags, 2))
    
    # Constraint: Total days per city must match requirements
    for idx, city in enumerate(cities):
        total_days = Sum([If(in_city[day][idx], 1, 0) for day in range(16)])
        solver.add(total_days == req_days[city])
    
    # Constraint: Must be in Split from day 7 to day 11 (inclusive)
    for day in range(6, 11):  # 0-indexed: days 6 to 10 correspond to days 7 to 11
        solver.add(in_city[day][city_index['Split']])
    
    # Constraint: Must be in London at least once between day 1 and day 7
    solver.add(Or([in_city[day][city_index['London']] for day in range(0, 7)]))
    
    # Constraint: Continuity between consecutive days
    for day in range(15):
        current_day_cities = [in_city[day][idx] for idx in range(4)]
        next_day_cities = [in_city[day+1][idx] for idx in range(4)]
        # There must be at least one city in common between consecutive days
        common_cities = Or([And(current_day_cities[idx], next_day_cities[idx]) for idx in range(4)])
        solver.add(common_cities)
    
    # Constraint: Direct flights only for travel days
    for day in range(16):
        for idx1 in range(4):
            for idx2 in range(idx1+1, 4):
                city1 = cities[idx1]
                city2 = cities[idx2]
                if (city1, city2) not in direct_set:
                    # Cannot be in both cities on the same day if no direct flight
                    solver.add(Not(And(in_city[day][idx1], in_city[day][idx2])))
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        # Extract the itinerary
        itinerary = []
        # For each city, find continuous intervals
        city_intervals = {city: [] for city in cities}
        for city in cities:
            idx = city_index[city]
            days_present = []
            for day in range(16):
                if is_true(model.eval(in_city[day][idx])):
                    days_present.append(day+1)  # 1-indexed days
            # Group consecutive days
            if not days_present:
                continue
            start = days_present[0]
            prev = days_present[0]
            for current in days_present[1:]:
                if current == prev + 1:
                    prev = current
                else:
                    city_intervals[city].append((start, prev))
                    start = current
                    prev = current
            city_intervals[city].append((start, prev))
        
        # Create itinerary list from intervals
        itinerary_list = []
        for city, intervals in city_intervals.items():
            for start, end in intervals:
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                itinerary_list.append({'day_range': day_range, 'place': city})
        
        # Sort by start day
        itinerary_list.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        
        # Output as JSON
        print(json.dumps({'itinerary': itinerary_list}))
    else:
        print('No solution found')

def is_true(x):
    return isinstance(x, BoolRef) and False

if __name__ == '__main__':
    main()