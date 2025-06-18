from z3 import *
import json

# Define cities and their required days
cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 'Stockholm', 'Istanbul', 'Amsterdam', 'Vienna', 'Split']
req_days = {
    'Prague': 5,
    'Brussels': 2,
    'Riga': 2,
    'Munich': 2,
    'Seville': 3,
    'Stockholm': 2,
    'Istanbul': 2,
    'Amsterdam': 3,
    'Vienna': 5,
    'Split': 3
}

# Direct flights as a set of tuples
direct_flights = {
    ('Riga', 'Stockholm'),
    ('Stockholm', 'Brussels'),
    ('Istanbul', 'Munich'),
    ('Istanbul', 'Riga'),
    ('Prague', 'Split'),
    ('Vienna', 'Brussels'),
    ('Vienna', 'Riga'),
    ('Split', 'Stockholm'),
    ('Munich', 'Amsterdam'),
    ('Split', 'Amsterdam'),
    ('Amsterdam', 'Stockholm'),
    ('Amsterdam', 'Riga'),
    ('Vienna', 'Stockholm'),
    ('Vienna', 'Istanbul'),
    ('Vienna', 'Seville'),
    ('Istanbul', 'Amsterdam'),
    ('Munich', 'Brussels'),
    ('Prague', 'Munich'),
    ('Riga', 'Munich'),
    ('Prague', 'Amsterdam'),
    ('Prague', 'Brussels'),
    ('Prague', 'Istanbul'),
    ('Istanbul', 'Stockholm'),
    ('Vienna', 'Prague'),
    ('Munich', 'Split'),
    ('Vienna', 'Amsterdam'),
    ('Prague', 'Stockholm'),
    ('Brussels', 'Seville'),
    ('Munich', 'Stockholm'),
    ('Istanbul', 'Brussels'),
    ('Amsterdam', 'Seville'),
    ('Vienna', 'Split'),
    ('Munich', 'Seville'),
    ('Riga', 'Brussels'),
    ('Prague', 'Riga'),
    ('Vienna', 'Munich')
}

# Create Z3 variables: in_city[day][city] for days 1 to 20
in_city = {}
for day in range(1, 21):
    for city in cities:
        in_city[(day, city)] = Bool(f"in_{day}_{city}")

solver = Solver()

# Constraint 1: For each day, the traveler is in exactly 1 or 2 cities
for day in range(1, 21):
    in_city_day = [in_city[(day, c)] for c in cities]
    solver.add(Or(Sum([If(var, 1, 0) for var in in_city_day]) == 1, 
               Sum([If(var, 1, 0) for var in in_city_day]) == 2))

# Constraint 2: For travel days (2 cities), ensure a direct flight exists between them
for day in range(1, 21):
    for i in range(len(cities)):
        for j in range(i + 1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            if (c1, c2) not in direct_flights and (c2, c1) not in direct_flights:
                solver.add(Not(And(in_city[(day, c1)], in_city[(day, c2)])))

# Constraint 3: Total days in each city
for city in cities:
    total_days = Sum([If(in_city[(d, city)], 1, 0) for d in range(1, 21)])
    solver.add(total_days == req_days[city])

# Fixed constraints
# Prague: must be there from day5 to day9 (inclusive)
for day in [5, 6, 7, 8, 9]:
    solver.add(in_city[(day, 'Prague')] == True)

# Riga: must be there on day15 and day16
solver.add(in_city[(15, 'Riga')] == True)
solver.add(in_city[(16, 'Riga')] == True)

# Stockholm: must be there on day16 and day17
solver.add(in_city[(16, 'Stockholm')] == True)
solver.add(in_city[(17, 'Stockholm')] == True)

# Vienna: at least one day between 1 and 5, and total 5 days
solver.add(Sum([If(in_city[(d, 'Vienna')], 1, 0) for d in range(1, 6)]) >= 1)

# Split: at least one day between 11 and 13, and total 3 days
solver.add(Sum([If(in_city[(d, 'Split')], 1, 0) for d in range(11, 14)]) >= 1)

# Check and get the model
if solver.check() == sat:
    model = solver.model()
    events = []

    # For contiguous blocks in each city
    for city in cities:
        days_in = []
        for day in range(1, 21):
            if is_true(model[in_city[(day, city)]]):
                days_in.append(day)
        
        if not days_in:
            continue
            
        # Find contiguous intervals
        intervals = []
        start = days_in[0]
        end = days_in[0]
        for i in range(1, len(days_in)):
            if days_in[i] == end + 1:
                end = days_in[i]
            else:
                intervals.append((start, end))
                start = days_in[i]
                end = days_in[i]
        intervals.append((start, end))
        
        for (s, e) in intervals:
            if s == e:
                day_str = f"Day {s}"
            else:
                day_str = f"Day {s}-{e}"
            events.append({
                'day_range': day_str,
                'place': city,
                'sort_key': (s, 1, city)  # type 1 for block
            })
    
    # Identify travel days (days with exactly two cities)
    travel_days = set()
    for day in range(1, 21):
        count = 0
        for city in cities:
            if is_true(model[in_city[(day, city)]]):
                count += 1
        if count == 2:
            travel_days.add(day)
    
    # Add single day events for travel days
    for day in travel_days:
        for city in cities:
            if is_true(model[in_city[(day, city)]]):
                events.append({
                    'day_range': f"Day {day}",
                    'place': city,
                    'sort_key': (day, 0, city)  # type 0 for single day
                })
    
    # Sort events by sort_key: (day, type, city) 
    # type 0 (single) comes before type 1 (block) for the same day
    events_sorted = sorted(events, key=lambda x: (x['sort_key'][0], x['sort_key'][1], x['sort_key'][2]))
    
    # Prepare the final itinerary list without sort_key
    itinerary = []
    for event in events_sorted:
        itinerary.append({'day_range': event['day_range'], 'place': event['place']})
    
    # Output as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")