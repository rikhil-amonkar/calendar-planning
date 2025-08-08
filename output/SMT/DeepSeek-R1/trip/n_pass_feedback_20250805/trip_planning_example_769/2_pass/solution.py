from z3 import *
import json

def main():
    city_names = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
    city_dict = {name: idx for idx, name in enumerate(city_names)}
    
    flights = [
        ('Porto', 'Amsterdam'),
        ('Munich', 'Amsterdam'),
        ('Reykjavik', 'Amsterdam'),
        ('Munich', 'Porto'),
        ('Prague', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Amsterdam', 'Santorini'),
        ('Prague', 'Amsterdam'),
        ('Prague', 'Munich')
    ]
    
    flight_pairs = []
    for a, b in flights:
        i1 = city_dict[a]
        i2 = city_dict[b]
        flight_pairs.append((i1, i2))
        flight_pairs.append((i2, i1))
    
    s = Solver()
    start = Int('start')
    s.add(start >= 0, start < 6)
    
    x = [Int(f'x_{i}') for i in range(16)]
    for i in range(16):
        s.add(x[i] >= 0, x[i] < 6)
    
    # Flight constraints: start to day0, and consecutive days
    s.add(If(start != x[0], 
             Or([And(start == c1, x[0] == c2) for (c1, c2) in flight_pairs]), 
             True))
    
    for i in range(15):
        s.add(If(x[i] != x[i+1], 
                 Or([And(x[i] == c1, x[i+1] == c2) for (c1, c2) in flight_pairs]), 
                 True))
    
    # Calculate total presence days per city
    total_presence = [0] * 6
    for c in range(6):
        presences = []
        # Day 1: if start city is c or end of day1 is c
        presences.append(If(Or(start == c, x[0] == c), 1, 0))
        for i in range(1, 16):
            presences.append(If(Or(x[i-1] == c, x[i] == c), 1, 0))
        total_presence[c] = Sum(presences)
    
    s.add(total_presence[city_dict['Porto']] == 5)
    s.add(total_presence[city_dict['Prague']] == 4)
    s.add(total_presence[city_dict['Reykjavik']] == 4)
    s.add(total_presence[city_dict['Santorini']] == 2)
    s.add(total_presence[city_dict['Amsterdam']] == 2)
    s.add(total_presence[city_dict['Munich']] == 4)
    
    # Travel days constraint: 16 days + travel days = 21
    travel_days = If(start != x[0], 1, 0)
    for i in range(15):
        travel_days += If(x[i] != x[i+1], 1, 0)
    s.add(travel_days == 5)
    
    # Event constraints
    c_re = city_dict['Reykjavik']
    wedding_days = []
    for day_index in [3, 4, 5, 6]:
        if day_index == 0:
            wedding_days.append(Or(start == c_re, x[0] == c_re))
        else:
            wedding_days.append(Or(x[day_index-1] == c_re, x[day_index] == c_re))
    s.add(Or(wedding_days))
    
    c_am = city_dict['Amsterdam']
    conf_days = []
    # Day 14 (index13) and day15 (index14)
    conf_days.append(Or(x[12] == c_am, x[13] == c_am))  # Presence on day14
    conf_days.append(Or(x[13] == c_am, x[14] == c_am))  # Presence on day15
    s.add(And(conf_days))
    
    c_mu = city_dict['Munich']
    meeting_days = []
    for day_index in [6, 7, 8, 9]:
        if day_index == 0:
            meeting_days.append(Or(start == c_mu, x[0] == c_mu))
        else:
            meeting_days.append(Or(x[day_index-1] == c_mu, x[day_index] == c_mu))
    s.add(Or(meeting_days))
    
    if s.check() == sat:
        m = s.model()
        start_val = m.evaluate(start).as_long()
        seq = [m.evaluate(x_i).as_long() for x_i in x]
        itinerary = []
        for i in range(16):
            city = city_names[seq[i]]
            itinerary.append({"day": i+1, "place": city})
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()