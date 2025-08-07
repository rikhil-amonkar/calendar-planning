from z3 import Solver, Int, Or, And, Sum, If, sat
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
    num_days = 16
    
    s_vars = [Int(f's_{i}') for i in range(num_days)]
    e_vars = [Int(f'e_{i}') for i in range(num_days)]
    
    for i in range(num_days):
        s.add(s_vars[i] >= 0, s_vars[i] < 6)
        s.add(e_vars[i] >= 0, e_vars[i] < 6)
    
    for i in range(num_days - 1):
        s.add(e_vars[i] == s_vars[i+1])
    
    for i in range(num_days):
        same_city = (s_vars[i] == e_vars[i])
        different_city = (s_vars[i] != e_vars[i])
        flight_exists = Or([And(s_vars[i] == c1, e_vars[i] == c2) for (c1, c2) in flight_pairs])
        s.add(If(different_city, flight_exists, True))
    
    travel_days = Sum([If(s_vars[i] != e_vars[i], 1, 0) for i in range(num_days)])
    s.add(travel_days == 5)
    
    porto, prague, reykjavik, santorini, amsterdam, munich = range(6)
    
    presence = [0] * 6
    for c in range(6):
        total = 0
        for i in range(num_days):
            total += If(Or(s_vars[i] == c, e_vars[i] == c), 1, 0)
        presence[c] = total
    
    s.add(presence[porto] == 5)
    s.add(presence[prague] == 4)
    s.add(presence[reykjavik] == 4)
    s.add(presence[santorini] == 2)
    s.add(presence[amsterdam] == 2)
    s.add(presence[munich] == 4)
    
    wedding_days = []
    for i in [3, 4, 5, 6]:
        wedding_days.append(Or(s_vars[i] == reykjavik, e_vars[i] == reykjavik))
    s.add(Or(wedding_days))
    
    s.add(Or(s_vars[13] == amsterdam, e_vars[13] == amsterdam))
    s.add(Or(s_vars[14] == amsterdam, e_vars[14] == amsterdam))
    
    meeting_days = []
    for i in [6, 7, 8, 9]:
        meeting_days.append(Or(s_vars[i] == munich, e_vars[i] == munich))
    s.add(Or(meeting_days))
    
    if s.check() == sat:
        m = s.model()
        s_vals = [m.evaluate(s_vars[i]).as_long() for i in range(num_days)]
        
        itinerary = []
        current_city = s_vals[0]
        start_day = 1
        for i in range(1, num_days):
            if s_vals[i] != current_city:
                end_day = i
                itinerary.append({
                    'day_range': f'Day {start_day}-{end_day}',
                    'place': city_names[current_city]
                })
                start_day = i + 1
                current_city = s_vals[i]
        itinerary.append({
            'day_range': f'Day {start_day}-16',
            'place': city_names[current_city]
        })
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == '__main__':
    main()