import z3
import json

def main():
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    n = len(cities)
    idx_rome = cities.index("Rome")
    idx_mykonos = cities.index("Mykonos")
    idx_krakow = cities.index("Krakow")
    
    days_list = [4, 3, 3, 3, 4, 4, 2]
    
    edges = [
        (0,2), (0,5), (0,1), (0,4), (0,3),
        (1,0), (1,2), (1,5),
        (2,0), (2,3), (2,1), (2,5),
        (3,2), (3,4), (3,5),
        (4,3), (4,5), (4,0),
        (5,4), (5,1), (5,0), (5,2), (5,6),
        (6,5)
    ]
    
    s = z3.Solver()
    
    order = [z3.Int('o%d' % i) for i in range(n)]
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    
    s.add(order[0] == idx_rome)
    s.add(order[6] == idx_krakow)
    s.add(z3.Distinct(order))
    
    days_arr = z3.Array('days_arr', z3.IntSort(), z3.IntSort())
    for i in range(n):
        days_arr = z3.Store(days_arr, i, days_list[i])
    
    start_days = [z3.Int('s%d' % i) for i in range(n)]
    end_days = [z3.Int('e%d' % i) for i in range(n)]
    
    s.add(start_days[0] == 1)
    s.add(end_days[0] == start_days[0] + days_arr[order[0]] - 1)
    
    for i in range(1, n):
        s.add(start_days[i] == end_days[i-1])
        s.add(end_days[i] == start_days[i] + days_arr[order[i]] - 1)
    
    s.add(end_days[6] == 17)
    
    mykonos_constraint = z3.Or([z3.And(order[i] == idx_mykonos, start_days[i] <= 6) for i in range(n)])
    s.add(mykonos_constraint)
    
    for k in range(n-1):
        edge_constraint = z3.Or([z3.And(order[k] == u, order[k+1] == v) for (u, v) in edges])
        s.add(edge_constraint)
    
    if s.check() == z3.sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(n)]
        s_vals = [m.evaluate(start_days[i]).as_long() for i in range(n)]
        e_vals = [m.evaluate(end_days[i]).as_long() for i in range(n)]
        
        itinerary = []
        for day in range(1, 18):
            for idx in range(n):
                if s_vals[idx] <= day <= e_vals[idx]:
                    city_name = cities[order_vals[idx]]
                    itinerary.append({"day": day, "city": city_name})
                    
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()