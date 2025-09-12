from z3 import *
import json

def main():
    # Cities and required days
    cities = ['Venice', 'Naples', 'Valencia', 'Stuttgart', 'Split', 'Amsterdam', 'Nice', 'Barcelona', 'Porto']
    required_days = {
        'Venice': 5,
        'Naples': 3,
        'Valencia': 5,
        'Stuttgart': 2,
        'Split': 5,
        'Amsterdam': 4,
        'Nice': 2,
        'Barcelona': 2,
        'Porto': 4
    }
    
    # Direct flights list
    direct_flights_list = [
        ('Venice', 'Nice'), ('Naples', 'Amsterdam'), ('Barcelona', 'Nice'), ('Amsterdam', 'Nice'),
        ('Stuttgart', 'Valencia'), ('Stuttgart', 'Porto'), ('Split', 'Stuttgart'), ('Split', 'Naples'),
        ('Valencia', 'Amsterdam'), ('Barcelona', 'Porto'), ('Valencia', 'Naples'), ('Venice', 'Amsterdam'),
        ('Barcelona', 'Naples'), ('Barcelona', 'Valencia'), ('Split', 'Amsterdam'), ('Barcelona', 'Venice'),
        ('Stuttgart', 'Amsterdam'), ('Naples', 'Nice'), ('Venice', 'Stuttgart'), ('Split', 'Barcelona'),
        ('Porto', 'Nice'), ('Barcelona', 'Stuttgart'), ('Venice', 'Naples'), ('Porto', 'Amsterdam'),
        ('Porto', 'Valencia'), ('Stuttgart', 'Naples'), ('Barcelona', 'Amsterdam')
    ]
    
    # Create symmetric allowed pairs
    allowed_pairs = set()
    for a, b in direct_flights_list:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    total_days = 24
    s = Solver()
    
    # Create a 2D array of Z3 booleans: in_city[day][city]
    in_city = [[Bool(f"day_{day}_{city}") for city in cities] for day in range(1, total_days+1)]
    
    # Constraint 1: Each day has at least one and at most two cities
    for day in range(total_days):
        day_vars = in_city[day]
        s.add(AtLeast(*day_vars, 1))
        s.add(AtMost(*day_vars, 2))
    
    # Constraint 2: Total days per city matches requirements
    for city_idx, city in enumerate(cities):
        s.add(Sum([If(in_city[day][city_idx], 1, 0) for day in range(total_days)]) == required_days[city])
    
    # Constraint 3: For days with two cities, they must be connected by a direct flight
    for day in range(total_days):
        day_vars = in_city[day]
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city_i = cities[i]
                city_j = cities[j]
                # If both cities are true on this day, then they must be connected
                both_true = And(day_vars[i], day_vars[j])
                s.add(Implies(both_true, Or(
                    *[(city_i == a and city_j == b) for (a, b) in allowed_pairs if a == city_i and b == city_j]
                )))
    
    # Constraint 4: Consecutive days must share at least one city
    for day in range(total_days-1):
        day_current = in_city[day]
        day_next = in_city[day+1]
        overlap = Or([And(day_current[i], day_next[i]) for i in range(len(cities))])
        s.add(overlap)
    
    # Special constraints
    # Venice must be present on days 6-10 (index 5 to 9)
    for day in [5,6,7,8,9]:  # 0-indexed: day5 is the 6th day
        s.add(in_city[day][cities.index('Venice')])
    
    # Barcelona must be present on days 5 and 6 (index 4 and 5)
    for day in [4,5]:
        s.add(in_city[day][cities.index('Barcelona')])
    
    # Nice must be present on days 23 and 24 (index 22 and 23)
    for day in [22,23]:
        s.add(in_city[day][cities.index('Nice')])
    
    # Naples must be present on one of days 18,19,20 (index 17,18,19)
    s.add(Or([
        in_city[17][cities.index('Naples')],
        in_city[18][cities.index('Naples')],
        in_city[19][cities.index('Naples')]
    ]))
    
    # Check feasibility
    if s.check() == sat:
        m = s.model()
        # Extract the assignment
        assignment = []
        for day in range(total_days):
            day_assignment = []
            for city_idx in range(len(cities)):
                if is_true(m.evaluate(in_city[day][city_idx])):
                    day_assignment.append(cities[city_idx])
            assignment.append(day_assignment)
        
        # Now, create segments for each city
        segments = []
        for city in cities:
            current_start = None
            for day in range(total_days):
                if city in assignment[day]:
                    if current_start is None:
                        current_start = day
                else:
                    if current_start is not None:
                        segments.append((current_start+1, day, city))
                        current_start = None
            if current_start is not None:
                segments.append((current_start+1, total_days, city))
        
        # Convert segments to itinerary format
        itinerary = []
        for start, end, city in segments:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()