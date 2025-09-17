from z3 import *
import json

def main():
    # Define cities and required days
    cities = ['Reykjavik', 'Stuttgart', 'Munich', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia']
    req_days = {
        'Reykjavik': 4,
        'Stuttgart': 4,
        'Munich': 3,
        'Istanbul': 4,
        'Vilnius': 4,
        'Seville': 3,
        'Geneva': 5,
        'Valencia': 5
    }
    
    n_days = 25
    n_cities = len(cities)
    c_index = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (undirected)
    direct_flights = [
        ('Geneva', 'Istanbul'),
        ('Reykjavik', 'Munich'),
        ('Stuttgart', 'Valencia'),
        ('Reykjavik', 'Stuttgart'),
        ('Stuttgart', 'Istanbul'),
        ('Munich', 'Geneva'),
        ('Istanbul', 'Vilnius'),
        ('Valencia', 'Seville'),
        ('Valencia', 'Istanbul'),
        ('Vilnius', 'Munich'),
        ('Seville', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Valencia', 'Geneva'),
        ('Valencia', 'Munich')
    ]
    
    # Create direct flight matrix
    direct_flight_matrix = [[False] * n_cities for _ in range(n_cities)]
    for (a, b) in direct_flights:
        i, j = c_index[a], c_index[b]
        direct_flight_matrix[i][j] = True
        direct_flight_matrix[j][i] = True
    
    # Initialize solver
    s = Solver()
    
    # in_city[i][d] means we are in city i on day d (1-indexed days, 0-indexed in array)
    in_city = [[Bool(f"in_city_{i}_{d}") for d in range(n_days)] for i in range(n_cities)]
    
    # Constraint 1: Each day has 1 or 2 cities
    for d in range(n_days):
        cities_on_d = [in_city[i][d] for i in range(n_cities)]
        s.add(Or(Sum([If(c, 1, 0) for c in cities_on_d]) == 1, Sum([If(c, 1, 0) for c in cities_on_d]) == 2))
    
    # Constraint 2: Total days per city
    for i, city in enumerate(cities):
        total = Sum([If(in_city[i][d], 1, 0) for d in range(n_days)])
        s.add(total == req_days[city])
    
    # Constraint 3: Fixed days
    # Reykjavik on days 1-4 (index 0-3)
    for d in range(4):
        s.add(in_city[c_index['Reykjavik']][d])
    # Istanbul on days 19-22 (index 18-21)
    for d in range(18, 22):
        s.add(in_city[c_index['Istanbul']][d])
    # Munich on days 13-15 (index 12-14)
    for d in range(12, 15):
        s.add(in_city[c_index['Munich']][d])
    # Stuttgart on day 4 and day 7 (index 3 and 6)
    s.add(in_city[c_index['Stuttgart']][3])
    s.add(in_city[c_index['Stuttgart']][6])
    
    # Constraint 4: Day transitions
    for d in range(1, n_days):
        prev = [in_city[i][d-1] for i in range(n_cities)]
        curr = [in_city[i][d] for i in range(n_cities)]
        count_prev = Sum([If(p, 1, 0) for p in prev])
        count_curr = Sum([If(c, 1, 0) for c in curr])
        
        # Case 1: Previous day has one city
        one_prev = (count_prev == 1)
        # The same city must be present today
        same_city = And([Implies(prev[i], curr[i]) for i in range(n_cities)])
        # Allow adding a new connected city
        new_city = Or([And(curr[j], Not(prev[j]), Or([And(prev[i], direct_flight_matrix[i][j]) for i in range(n_cities)])) for j in range(n_cities)])
        case1 = And(one_prev, Or(And(count_curr == 1, same_city), 
                                 And(count_curr == 2, same_city, new_city)))
        
        # Case 2: Previous day has two cities
        two_prev = (count_prev == 2)
        # Today must have one city from yesterday
        one_curr = (count_curr == 1)
        curr_city_was_prev = And([Implies(curr[i], prev[i]) for i in range(n_cities)])
        case2 = And(two_prev, one_curr, curr_city_was_prev)
        
        s.add(Or(case1, case2))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        assignment = [[m.evaluate(in_city[i][d]) for d in range(n_days)] for i in range(n_cities)]
        
        # Convert assignment to list of days per city
        city_days = {}
        for i, city in enumerate(cities):
            days = [d+1 for d in range(n_days) if is_true(assignment[i][d])]
            city_days[city] = days
        
        # Create itinerary segments
        itinerary = []
        for city, days in city_days.items():
            days.sort()
            segments = []
            start = days[0]
            for i in range(1, len(days)):
                if days[i] != days[i-1] + 1:
                    segments.append((start, days[i-1]))
                    start = days[i]
            segments.append((start, days[-1]))
            
            for seg in segments:
                start_day, end_day = seg
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append((start_day, end_day, city, day_range))
        
        # Sort segments by start day
        itinerary.sort(key=lambda x: x[0])
        result = [{"day_range": seg[3], "place": seg[2]} for seg in itinerary]
        
        print(json.dumps({"itinerary": result}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()