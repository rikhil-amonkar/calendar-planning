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
    
    # Flight constraints
    s.add(If(start != x[0], 
             Or([And(start == c1, x[0] == c2) for (c1, c2) in flight_pairs]), 
             True))
    
    for i in range(15):
        s.add(If(x[i] != x[i+1], 
                 Or([And(x[i] == c1, x[i+1] == c2) for (c1, c2) in flight_pairs]), 
                 True))
    
    # Presence days calculation
    presence_per_city = [0] * 6
    for c in range(6):
        presences = []
        # Day 1: present if in city at start or end
        presences.append(If(Or(start == c, x[0] == c), 1, 0))
        # Days 2-16: present if in city at start (x[i-1]) or end (x[i])
        for i in range(1, 16):
            presences.append(If(Or(x[i-1] == c, x[i] == c), 1, 0))
        presence_per_city[c] = Sum(presences)
    
    # Required presence days
    s.add(presence_per_city[city_dict['Porto']] == 5)
    s.add(presence_per_city[city_dict['Prague']] == 4)
    s.add(presence_per_city[city_dict['Reykjavik']] == 4)
    s.add(presence_per_city[city_dict['Santorini']] == 2)
    s.add(presence_per_city[city_dict['Amsterdam']] == 2)
    s.add(presence_per_city[city_dict['Munich']] == 4)
    
    # Travel days must be exactly 5
    travel_days = If(start != x[0], 1, 0)
    for i in range(15):
        travel_days += If(x[i] != x[i+1], 1, 0)
    s.add(travel_days == 5)
    
    # Event constraints
    # Reykjavik wedding must be attended on days 4-7
    c_re = city_dict['Reykjavik']
    wedding_days = []
    for day in [3, 4, 5, 6]:  # Days 4-7 (0-indexed positions 3-6)
        if day == 0:
            # First day: check start or end
            wedding_days.append(Or(start == c_re, x[0] == c_re))
        else:
            wedding_days.append(Or(x[day-1] == c_re, x[day] == c_re))
    s.add(Or(wedding_days))
    
    # Amsterdam conference on days 14-15
    c_am = city_dict['Amsterdam']
    # Must be present on both days
    s.add(Or(x[13] == c_am, x[14] == c_am))  # Day 14
    s.add(Or(x[14] == c_am, x[15] == c_am))  # Day 15
    
    # Munich meeting on days 7-10
    c_mu = city_dict['Munich']
    meeting_days = []
    for day in [6, 7, 8, 9]:  # Days 7-10 (0-indexed positions 6-9)
        if day == 0:
            meeting_days.append(Or(start == c_mu, x[0] == c_mu))
        else:
            meeting_days.append(Or(x[day-1] == c_mu, x[day] == c_mu))
    s.add(Or(meeting_days))
    
    if s.check() == sat:
        m = s.model()
        start_val = m.evaluate(start).as_long()
        seq = [m.evaluate(x_i).as_long() for x_i in x]
        
        # Generate day ranges considering travel days
        itinerary = []
        current_city = city_names[seq[0]]
        start_day = 1
        # Track current segment
        for day_idx in range(1, 16):
            if seq[day_idx] != seq[day_idx-1]:
                # End current segment at previous day
                end_day = day_idx
                itinerary.append({
                    'day_range': f'Day {start_day}-{end_day}',
                    'place': current_city
                })
                # Start new segment
                start_day = day_idx + 1
                current_city = city_names[seq[day_idx]]
        # Add last segment
        itinerary.append({
            'day_range': f'Day {start_day}-16',
            'place': current_city
        })
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == '__main__':
    main()