from z3 import *
import json

def main():
    city_list = ['Vienna', 'Barcelona', 'Edinburgh', 'Krakow', 'Riga', 'Hamburg', 'Paris', 'Stockholm']
    n_days = 16
    n_cities = 8

    c_index = {city: idx for idx, city in enumerate(city_list)}
    idx_city = {idx: city for idx, city in enumerate(city_list)}

    edges = set()
    bidirectional_pairs = [
        ('Hamburg', 'Stockholm'),
        ('Vienna', 'Stockholm'),
        ('Paris', 'Edinburgh'),
        ('Riga', 'Barcelona'),
        ('Paris', 'Riga'),
        ('Krakow', 'Barcelona'),
        ('Edinburgh', 'Stockholm'),
        ('Paris', 'Krakow'),
        ('Krakow', 'Stockholm'),
        ('Riga', 'Edinburgh'),
        ('Barcelona', 'Stockholm'),
        ('Paris', 'Stockholm'),
        ('Krakow', 'Edinburgh'),
        ('Vienna', 'Hamburg'),
        ('Paris', 'Hamburg'),
        ('Riga', 'Stockholm'),
        ('Hamburg', 'Barcelona'),
        ('Vienna', 'Barcelona'),
        ('Krakow', 'Vienna'),
        ('Barcelona', 'Edinburgh'),
        ('Paris', 'Barcelona'),
        ('Hamburg', 'Edinburgh'),
        ('Paris', 'Vienna'),
        ('Vienna', 'Riga')
    ]
    
    for (a, b) in bidirectional_pairs:
        a_idx = c_index[a]
        b_idx = c_index[b]
        edges.add((a_idx, b_idx))
        edges.add((b_idx, a_idx))
    
    edges.add((c_index['Riga'], c_index['Hamburg']))

    solver = Solver()

    s_d = [Int(f's_{d}') for d in range(n_days)]
    travel_d = [Bool(f'travel_{d}') for d in range(n_days)]
    next_city_d = [Int(f'next_city_{d}') for d in range(n_days)]

    for d in range(n_days):
        solver.add(s_d[d] >= 0, s_d[d] < n_cities)
        solver.add(next_city_d[d] >= 0, next_city_d[d] < n_cities)

    solver.add(s_d[0] == c_index['Paris'])

    for d in range(n_days - 1):
        solver.add(s_d[d+1] == If(travel_d[d], next_city_d[d], s_d[d]))

    for d in range(n_days):
        edge_options = []
        for (u, v) in edges:
            edge_options.append(And(s_d[d] == u, next_city_d[d] == v))
        solver.add(Implies(travel_d[d], Or(edge_options)))

    def x(d, c):
        return Or(s_d[d] == c, And(travel_d[d], next_city_d[d] == c))

    paris_idx = c_index['Paris']
    solver.add(x(0, paris_idx))
    solver.add(x(1, paris_idx))
    for d in range(2, n_days):
        solver.add(Not(x(d, paris_idx)))

    hamburg_idx = c_index['Hamburg']
    solver.add(x(9, hamburg_idx))
    solver.add(x(10, hamburg_idx))
    for d in list(range(0, 9)) + list(range(11, n_days)):
        solver.add(Not(x(d, hamburg_idx)))

    total_days = [0] * n_cities
    for c in range(n_cities):
        total_days[c] = Sum([If(x(d, c), 1, 0) for d in range(n_days)])
    
    solver.add(total_days[c_index['Vienna']] == 4)
    solver.add(total_days[c_index['Barcelona']] == 2)
    solver.add(total_days[c_index['Edinburgh']] == 4)
    solver.add(total_days[c_index['Krakow']] == 3)
    solver.add(total_days[c_index['Riga']] == 4)
    solver.add(total_days[c_index['Hamburg']] == 2)
    solver.add(total_days[c_index['Paris']] == 2)
    solver.add(total_days[c_index['Stockholm']] == 2)

    edinburgh_idx = c_index['Edinburgh']
    solver.add(Or(x(11, edinburgh_idx), x(12, edinburgh_idx), x(13, edinburgh_idx), x(14, edinburgh_idx)))
    for d in range(0, 11):
        solver.add(Not(x(d, edinburgh_idx)))

    stockholm_idx = c_index['Stockholm']
    solver.add(Or(x(14, stockholm_idx), x(15, stockholm_idx)))

    total_travel = Sum([If(travel_d[d], 1, 0) for d in range(n_days)])
    solver.add(total_travel == 7)

    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        for d in range(n_days):
            day_num = d + 1
            start_city_val = m.evaluate(s_d[d]).as_long()
            start_city = idx_city[start_city_val]
            itinerary.append({"day": day_num, "place": start_city})
            if m.evaluate(travel_d[d]):
                next_city_val = m.evaluate(next_city_d[d]).as_long()
                next_city = idx_city[next_city_val]
                if next_city != start_city:
                    itinerary.append({"day": day_num, "place": next_city})
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()