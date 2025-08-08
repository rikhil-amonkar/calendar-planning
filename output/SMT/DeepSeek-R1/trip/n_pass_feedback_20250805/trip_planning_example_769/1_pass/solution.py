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
    for pair in flights:
        c1, c2 = pair
        flight_pairs.append((city_dict[c1], city_dict[c2]))
        flight_pairs.append((city_dict[c2], city_dict[c1]))
    
    s = Solver()
    x = [Int(f'x_{i}') for i in range(16)]
    
    for i in range(16):
        s.add(And(x[i] >= 0, x[i] < 6))
    
    for i in range(15):
        c1 = x[i]
        c2 = x[i+1]
        s.add(If(c1 != c2, 
                 Or([And(c1 == p1, c2 == p2) for (p1, p2) in flight_pairs]), 
                 True))
    
    total_days = [0] * 6
    for c in range(6):
        presences = []
        presences.append(If(x[0] == c, 1, 0))
        for i in range(1, 16):
            presences.append(If(Or(x[i-1] == c, x[i] == c), 1, 0))
        total_days[c] = Sum(presences)
    
    s.add(total_days[city_dict['Porto']] == 5)
    s.add(total_days[city_dict['Prague']] == 4)
    s.add(total_days[city_dict['Reykjavik']] == 4)
    s.add(total_days[city_dict['Santorini']] == 2)
    s.add(total_days[city_dict['Amsterdam']] == 2)
    s.add(total_days[city_dict['Munich']] == 4)
    
    total_days_sum = Sum([total_days[i] for i in range(6)])
    s.add(total_days_sum == 21)
    
    c_re = city_dict['Reykjavik']
    wedding_constraints = []
    for i in [3, 4, 5, 6]:
        if i == 0:
            wedding_constraints.append(x[0] == c_re)
        else:
            wedding_constraints.append(Or(x[i-1] == c_re, x[i] == c_re))
    s.add(Or(wedding_constraints))
    
    c_am = city_dict['Amsterdam']
    s.add(Or(x[12] == c_am, x[13] == c_am))
    s.add(Or(x[13] == c_am, x[14] == c_am))
    
    c_mu = city_dict['Munich']
    friend_constraints = []
    for i in [6, 7, 8, 9]:
        if i == 0:
            friend_constraints.append(x[0] == c_mu)
        else:
            friend_constraints.append(Or(x[i-1] == c_mu, x[i] == c_mu))
    s.add(Or(friend_constraints))
    
    if s.check() == sat:
        m = s.model()
        seq = [m.evaluate(x[i]).as_long() for i in range(16)]
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