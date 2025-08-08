from z3 import *

city_names = ['Reykjavik', 'Stuttgart', 'Manchester', 'Istanbul', 'Riga', 'Bucharest', 'Vienna', 'Florence']
min_days = [2, 3, 2, 2, 2, 3, 2, 3]
max_days = [4, 5, 3, 3, 3, 4, 3, 4]

graph = {
    'Reykjavik': ['Vienna', 'Stuttgart', 'Manchester', 'Florence', 'Istanbul', 'Riga', 'Bucharest'],
    'Stuttgart': ['Reykjavik', 'Manchester', 'Florence', 'Istanbul', 'Riga', 'Bucharest'],
    'Manchester': ['Reykjavik', 'Stuttgart', 'Florence', 'Istanbul', 'Riga', 'Bucharest'],
    'Istanbul': ['Reykjavik', 'Stuttgart', 'Manchester', 'Florence', 'Riga', 'Bucharest'],
    'Riga': ['Reykjavik', 'Stuttgart', 'Manchester', 'Florence', 'Istanbul', 'Bucharest'],
    'Bucharest': ['Reykjavik', 'Stuttgart', 'Manchester', 'Florence', 'Istanbul', 'Riga'],
    'Vienna': ['Reykjavik', 'Florence'],
    'Florence': ['Reykjavik', 'Stuttgart', 'Manchester', 'Istanbul', 'Riga', 'Bucharest', 'Vienna']
}

allowed_set = set()
for idx, city in enumerate(city_names):
    for neighbor in graph[city]:
        j = city_names.index(neighbor)
        allowed_set.add((idx, j))

s = Solver()

# Day assignment for each day (1 to 23)
days = [Int(f"day_{d}") for d in range(1, 24)]
for d in range(23):
    s.add(days[d] >= 0, days[d] < 8)

# Flight connectivity between consecutive days
for d in range(22):
    current_city = days[d]
    next_city = days[d+1]
    s.add(If(current_city != next_city, 
             Or([And(current_city == i, next_city == j) for (i, j) in allowed_set]),
             True))

# Contiguous blocks for each city
for city_idx in range(8):
    # Track start and end days for each city
    start_day = Int(f"start_{city_idx}")
    end_day = Int(f"end_{city_idx}")
    s.add(start_day >= 1, start_day <= 23)
    s.add(end_day >= 1, end_day <= 23)
    s.add(start_day <= end_day)
    
    # Duration must be within min/max
    duration = end_day - start_day + 1
    s.add(duration >= min_days[city_idx], duration <= max_days[city_idx])
    
    # All days in block must be this city
    for d in range(23):
        day_num = d + 1
        s.add(If(And(day_num >= start_day, day_num <= end_day),
                 days[d] == city_idx,
                 days[d] != city_idx))

# All cities must appear exactly once
for city_idx in range(8):
    s.add(Or([days[d] == city_idx for d in range(23)]))
    s.add(Not(Or(And(days[0] == city_idx, days[0] != days[1]),
                 And(days[22] == city_idx, days[22] != days[21]),
                 Or([And(days[d] == city_idx, 
                         days[d-1] != city_idx, 
                         days[d+1] != city_idx) 
                     for d in range(1, 22)]))))

# Solve and format output
if s.check() == sat:
    model = s.model()
    day_assignments = [model.evaluate(days[d]).as_long() for d in range(23)]
    
    # Build itinerary blocks
    current_city = day_assignments[0]
    start = 1
    plan = []
    for d in range(1, 23):
        if day_assignments[d] != current_city:
            end = d
            plan.append({
                'day_range': f"Day {start}-{end}",
                'place': city_names[current_city]
            })
            start = d + 1
            current_city = day_assignments[d]
    plan.append({
        'day_range': f"Day {start}-23",
        'place': city_names[current_city]
    })
    
    result = {'itinerary': plan}
    print(f"Plan found: {result}")
else:
    print("No valid plan found")