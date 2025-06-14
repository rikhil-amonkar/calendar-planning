from z3 import *

def main():
    cities = ["Paris", "Vienna", "Barcelona", "Edinburgh", "Krakow", "Riga", "Hamburg", "Stockholm"]
    n_days = 16
    n_cities = len(cities)
    
    city_index = {name: idx for idx, name in enumerate(cities)}
    req_days = [2, 4, 2, 4, 3, 4, 2, 2]
    
    directed_edges = []
    def add_bidirectional(a, b):
        directed_edges.append((a, b))
        directed_edges.append((b, a))
    
    add_bidirectional(city_index['Hamburg'], city_index['Stockholm'])
    add_bidirectional(city_index['Vienna'], city_index['Stockholm'])
    add_bidirectional(city_index['Paris'], city_index['Edinburgh'])
    add_bidirectional(city_index['Riga'], city_index['Barcelona'])
    add_bidirectional(city_index['Paris'], city_index['Riga'])
    add_bidirectional(city_index['Krakow'], city_index['Barcelona'])
    add_bidirectional(city_index['Edinburgh'], city_index['Stockholm'])
    add_bidirectional(city_index['Paris'], city_index['Krakow'])
    add_bidirectional(city_index['Krakow'], city_index['Stockholm'])
    add_bidirectional(city_index['Riga'], city_index['Edinburgh'])
    add_bidirectional(city_index['Barcelona'], city_index['Stockholm'])
    add_bidirectional(city_index['Paris'], city_index['Stockholm'])
    add_bidirectional(city_index['Krakow'], city_index['Edinburgh'])
    add_bidirectional(city_index['Vienna'], city_index['Hamburg'])
    add_bidirectional(city_index['Paris'], city_index['Hamburg'])
    add_bidirectional(city_index['Riga'], city_index['Stockholm'])
    add_bidirectional(city_index['Hamburg'], city_index['Barcelona'])
    add_bidirectional(city_index['Vienna'], city_index['Barcelona'])
    add_bidirectional(city_index['Krakow'], city_index['Vienna'])
    directed_edges.append((city_index['Riga'], city_index['Hamburg']))
    add_bidirectional(city_index['Barcelona'], city_index['Edinburgh'])
    add_bidirectional(city_index['Paris'], city_index['Barcelona'])
    add_bidirectional(city_index['Hamburg'], city_index['Edinburgh'])
    add_bidirectional(city_index['Paris'], city_index['Vienna'])
    add_bidirectional(city_index['Vienna'], city_index['Riga'])
    
    s = Solver()
    
    start = [Int('start_%d' % i) for i in range(n_days)]
    end = [Int('end_%d' % i) for i in range(n_days)]
    
    domain_constraints = []
    for i in range(n_days):
        domain_constraints.append(And(start[i] >= 0, start[i] < n_cities))
        domain_constraints.append(And(end[i] >= 0, end[i] < n_cities))
    s.add(domain_constraints)
    
    travel_day = [start[i] != end[i] for i in range(n_days)]
    total_travel_days = Sum([If(td, 1, 0) for td in travel_day])
    s.add(total_travel_days == 7)
    
    continuity = [end[i] == start[i+1] for i in range(n_days-1)]
    s.add(continuity)
    
    flight_constraints = []
    for i in range(n_days):
        edge_conds = []
        for (u, v) in directed_edges:
            edge_conds.append(And(start[i] == u, end[i] == v))
        flight_constraints.append(If(travel_day[i], Or(edge_conds), True))
    s.add(flight_constraints)
    
    city_days = []
    for c in range(n_cities):
        total = Sum([If(Or(start[i] == c, end[i] == c), 1, 0) for i in range(n_days)])
        city_days.append(total)
    for c in range(n_cities):
        s.add(city_days[c] == req_days[c])
    
    specific_constraints = []
    specific_constraints.append(start[0] == city_index['Paris'])
    specific_constraints.append(Or(start[1] == city_index['Paris'], end[1] == city_index['Paris']))
    specific_constraints.append(Or(start[9] == city_index['Hamburg'], end[9] == city_index['Hamburg']))
    specific_constraints.append(Or(start[10] == city_index['Hamburg'], end[10] == city_index['Hamburg']))
    for i in range(11, 15):
        specific_constraints.append(Or(start[i] == city_index['Edinburgh'], end[i] == city_index['Edinburgh']))
    specific_constraints.append(Or(start[14] == city_index['Stockholm'], end[14] == city_index['Stockholm']))
    specific_constraints.append(Or(start[15] == city_index['Stockholm'], end[15] == city_index['Stockholm']))
    specific_constraints.append(Or(start[15] == city_index['Barcelona'], end[15] == city_index['Barcelona']))
    s.add(specific_constraints)
    
    if s.check() == sat:
        m = s.model()
        for i in range(n_days):
            s_val = m.evaluate(start[i])
            e_val = m.evaluate(end[i])
            s_city = cities[s_val.as_long()]
            e_city = cities[e_val.as_long()]
            if s_val.as_long() == e_val.as_long():
                print(f"Day {i+1}: Stay in {s_city}")
            else:
                print(f"Day {i+1}: Travel from {s_city} to {e_city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()