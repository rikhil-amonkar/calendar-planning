from z3 import *
import json

def main():
    # City mapping
    cities = {0: 'Paris', 1: 'Oslo', 2: 'Porto', 3: 'Geneva', 4: 'Reykjavik'}
    
    # Direct flights (symmetric)
    flight_set = set([
        (0,1), (1,0), (3,1), (1,3), (2,0), (0,2), (3,0), (0,3),
        (3,2), (2,3), (0,4), (4,0), (4,1), (1,4), (2,1), (1,2)
    ])
    
    solver = Solver()
    num_days = 23
    days = list(range(1, num_days+1))
    
    # Arrays for start and end city for each day
    start_city = [Int(f'start_city_{d}') for d in days]
    end_city = [Int(f'end_city_{d}') for d in days]
    
    # Constraint: city values must be between 0 and 4
    for d in days:
        solver.add(start_city[d-1] >= 0, start_city[d-1] <= 4)
        solver.add(end_city[d-1] >= 0, end_city[d-1] <= 4)
    
    # Fixed constraints: Geneva on days 1-7 (entire day)
    for d in range(1, 8):
        solver.add(start_city[d-1] == 3)
        solver.add(end_city[d-1] == 3)
    
    # Fixed constraints: Oslo on days 19-23 (at least part of the day)
    for d in range(19, 24):
        solver.add(Or(start_city[d-1] == 1, end_city[d-1] == 1))
    
    # Continuity constraint
    for d in range(1, num_days):
        solver.add(end_city[d-1] == start_city[d])
    
    # Direct flight constraints for travel days
    for d in days:
        c1 = start_city[d-1]
        c2 = end_city[d-1]
        # If start and end are different, then must have a direct flight
        cond = Or([And(c1 == a, c2 == b) for (a, b) in flight_set])
        solver.add(If(c1 != c2, cond, True))
    
    # Calculate total days per city
    city_days = [0] * 5
    for c in range(5):
        total = 0
        for d in days:
            in_day = Or(start_city[d-1] == c, end_city[d-1] == c)
            total += If(in_day, 1, 0)
        city_days[c] = total
    
    # Required days per city
    solver.add(city_days[0] == 6)  # Paris
    solver.add(city_days[1] == 5)  # Oslo
    solver.add(city_days[2] == 7)  # Porto
    solver.add(city_days[3] == 7)  # Geneva
    solver.add(city_days[4] == 2)  # Reykjavik
    
    # Geneva only on days 1-7
    for d in range(8, num_days+1):
        solver.add(Not(Or(start_city[d-1] == 3, end_city[d-1] == 3)))
    
    # Oslo only on days 19-23
    for d in range(1, 19):
        solver.add(Not(Or(start_city[d-1] == 1, end_city[d-1] == 1)))
    
    # Check feasibility
    if solver.check() != sat:
        print('{"itinerary": []}')
        return
    
    model = solver.model()
    itinerary = []
    
    # Determine presence for each city each day
    presence = {c: [] for c in cities.values()}
    for d in days:
        start_val = model.eval(start_city[d-1]).as_long()
        end_val = model.eval(end_city[d-1]).as_long()
        cities_present = set()
        cities_present.add(cities[start_val])
        if start_val != end_val:
            cities_present.add(cities[end_val])
        for city in cities_present:
            presence[city].append(d)
    
    # Group consecutive days for each city
    output_list = []
    for city, days_list in presence.items():
        days_list.sort()
        if not days_list:
            continue
        ranges = []
        start = days_list[0]
        prev = days_list[0]
        for day in days_list[1:]:
            if day == prev + 1:
                prev = day
            else:
                ranges.append((start, prev))
                start = day
                prev = day
        ranges.append((start, prev))
        
        for (s, e) in ranges:
            if s == e:
                day_range_str = f"Day {s}"
            else:
                day_range_str = f"Day {s}-{e}"
            output_list.append({"day_range": day_range_str, "place": city})
    
    # Sort output by start day
    output_list.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
    print(json.dumps({"itinerary": output_list}))

if __name__ == '__main__':
    main()