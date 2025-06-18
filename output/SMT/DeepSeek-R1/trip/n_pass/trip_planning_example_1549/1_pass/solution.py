from z3 import *

def main():
    cities = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
    days = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]
    
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    flight_list_str = [
        ("Riga", "Prague"),
        ("Stockholm", "Milan"),
        ("Riga", "Milan"),
        ("Lisbon", "Stockholm"),
        ("Stockholm", "Santorini"),
        ("Naples", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Naples", "Milan"),
        ("Lisbon", "Naples"),
        ("Riga", "Tallinn"),
        ("Tallinn", "Prague"),
        ("Stockholm", "Warsaw"),
        ("Riga", "Warsaw"),
        ("Lisbon", "Riga"),
        ("Riga", "Stockholm"),
        ("Lisbon", "Porto"),
        ("Lisbon", "Prague"),
        ("Milan", "Porto"),
        ("Prague", "Milan"),
        ("Lisbon", "Milan"),
        ("Warsaw", "Porto"),
        ("Warsaw", "Tallinn"),
        ("Santorini", "Milan"),
        ("Stockholm", "Prague"),
        ("Stockholm", "Tallinn"),
        ("Warsaw", "Milan"),
        ("Santorini", "Naples"),
        ("Warsaw", "Prague")
    ]
    
    graph_edges = set()
    for (u_str, v_str) in flight_list_str:
        u = city_index[u_str]
        v = city_index[v_str]
        graph_edges.add((min(u, v), max(u, v)))
    
    edges_list = list(graph_edges)
    
    pos = [Int('pos_%d' % i) for i in range(10)]
    start = [Int('start_%d' % i) for i in range(10)]
    
    s = Solver()
    
    for i in range(10):
        s.add(pos[i] >= 0, pos[i] <= 9)
    
    s.add(Distinct(pos))
    
    s.add(start[0] == 1)
    
    for k in range(1, 10):
        prev_city_duration = days[pos[k-1]]
        s.add(start[k] == start[k-1] + prev_city_duration - 1)
    
    last_city_duration = days[pos[9]]
    s.add(start[9] + last_city_duration - 1 == 28)
    
    for k in range(9):
        a = pos[k]
        b = pos[k+1]
        edge_constraint = Or([Or(And(a == u, b == v), And(a == v, b == u)) for (u, v) in edges_list])
        s.add(edge_constraint)
    
    for k in range(10):
        s.add(If(pos[k] == 8, And(start[k] >= 2, start[k] <= 8), True))
        s.add(If(pos[k] == 1, And(start[k] >= 16, start[k] <= 20), True))
        s.add(If(pos[k] == 5, And(start[k] >= 22, start[k] <= 26), True))
    
    if s.check() == sat:
        m = s.model()
        pos_val = [m.evaluate(pos[i]).as_long() for i in range(10)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(10)]
        
        itinerary = []
        
        for k in range(10):
            city_idx = pos_val[k]
            city_name = cities[city_idx]
            s_day = start_val[k]
            duration = days[city_idx]
            e_day = s_day + duration - 1
            
            if s_day == e_day:
                day_range_str = "Day %d" % s_day
            else:
                day_range_str = "Day %d-%d" % (s_day, e_day)
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            if k < 9:
                flight_day = e_day
                itinerary.append({"day_range": "Day %d" % flight_day, "place": city_name})
                next_city_idx = pos_val[k+1]
                next_city_name = cities[next_city_idx]
                itinerary.append({"day_range": "Day %d" % flight_day, "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()