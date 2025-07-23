from z3 import *

def main():
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    city2idx = {city: idx for idx, city in enumerate(cities)}
    
    given_edges = [
        ('Krakow', 'Split'), ('Split', 'Athens'), ('Edinburgh', 'Krakow'), ('Venice', 'Stuttgart'),
        ('Krakow', 'Stuttgart'), ('Edinburgh', 'Stuttgart'), ('Stuttgart', 'Athens'), ('Venice', 'Edinburgh'),
        ('Athens', 'Mykonos'), ('Venice', 'Athens'), ('Stuttgart', 'Split'), ('Edinburgh', 'Athens')
    ]
    
    flight_edges = []
    for u, v in given_edges:
        u_idx = city2idx[u]
        v_idx = city2idx[v]
        flight_edges.append((u_idx, v_idx))
        flight_edges.append((v_idx, u_idx))
    
    x = [Int('x%d' % i) for i in range(21)]
    s = Solver()
    
    for i in range(21):
        s.add(And(x[i] >= 0, x[i] < 7))
    
    for i in range(20):
        s.add(Implies(
            x[i] != x[i+1],
            Or([And(x[i] == a, x[i+1] == b) for (a, b) in flight_edges])
        ))
    
    totals = [0] * 7
    for a in range(7):
        total_expr = 0
        for i in range(1, 21):
            cond = Or(x[i-1] == a, x[i] == a)
            total_expr += If(cond, 1, 0)
        totals[a] = total_expr
    
    s.add(totals[city2idx['Stuttgart']] == 3)
    s.add(totals[city2idx['Edinburgh']] == 4)
    s.add(totals[city2idx['Athens']] == 4)
    s.add(totals[city2idx['Split']] == 2)
    s.add(totals[city2idx['Krakow']] == 4)
    s.add(totals[city2idx['Venice']] == 5)
    s.add(totals[city2idx['Mykonos']] == 4)
    
    s.add(sum(totals) == 26)
    
    stuttgart_days = []
    for day in [11, 12, 13]:
        stuttgart_days.append(Or(x[day-1] == city2idx['Stuttgart'], x[day] == city2idx['Stuttgart']))
    s.add(Or(stuttgart_days))
    
    split_days = []
    for day in [13, 14]:
        split_days.append(Or(x[day-1] == city2idx['Split'], x[day] == city2idx['Split']))
    s.add(Or(split_days))
    
    krakow_days = []
    for day in [8, 9, 10, 11]:
        krakow_days.append(Or(x[day-1] == city2idx['Krakow'], x[day] == city2idx['Krakow']))
    s.add(Or(krakow_days))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 21):
            city_index = model[x[day]].as_long()
            city_name = cities[city_index]
            itinerary.append({"day": day, "place": city_name})
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()