from z3 import *

def main():
    cities = ["Oslo", "Helsinki", "Edinburgh", "Riga", "Tallinn", "Budapest", "Vilnius", "Porto", "Geneva"]
    city_to_index = {name: idx for idx, name in enumerate(cities)}
    days_required = [2, 2, 3, 2, 5, 5, 5, 5, 4]  # index aligned with cities

    bidirectional = [
        ("Porto", "Oslo"),
        ("Edinburgh", "Budapest"),
        ("Edinburgh", "Geneva"),
        ("Edinburgh", "Porto"),
        ("Vilnius", "Helsinki"),
        ("Riga", "Oslo"),
        ("Geneva", "Oslo"),
        ("Edinburgh", "Oslo"),
        ("Edinburgh", "Helsinki"),
        ("Vilnius", "Oslo"),
        ("Riga", "Helsinki"),
        ("Budapest", "Geneva"),
        ("Helsinki", "Budapest"),
        ("Helsinki", "Oslo"),
        ("Edinburgh", "Riga"),
        ("Tallinn", "Helsinki"),
        ("Geneva", "Porto"),
        ("Budapest", "Oslo"),
        ("Helsinki", "Geneva"),
        ("Tallinn", "Oslo")
    ]
    
    directed = [
        ("Riga", "Tallinn"),
        ("Tallinn", "Vilnius"),
        ("Riga", "Vilnius")
    ]
    
    edges = set()
    for a, b in bidirectional:
        a_idx = city_to_index[a]
        b_idx = city_to_index[b]
        edges.add((a_idx, b_idx))
        edges.add((b_idx, a_idx))
    for a, b in directed:
        a_idx = city_to_index[a]
        b_idx = city_to_index[b]
        edges.add((a_idx, b_idx))
    
    edges_list = list(edges)
    
    s = Solver()
    order = [Int(f'order_{i}') for i in range(9)]
    
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    def get_days_req(idx):
        return If(idx == 0, 2,
            If(idx == 1, 2,
            If(idx == 2, 3,
            If(idx == 3, 2,
            If(idx == 4, 5,
            If(idx == 5, 5,
            If(idx == 6, 5,
            If(idx == 7, 5,
            4))))))))
    
    oslo_conds = []
    tallinn_conds = []
    for i in range(9):
        sum_expr = 0
        for j in range(i):
            d_req = get_days_req(order[j])
            sum_expr += (d_req - 1)
        start_day_i = 1 + sum_expr
        oslo_conds.append(And(order[i] == 0, start_day_i >= 23))
        tallinn_conds.append(And(order[i] == 4, start_day_i <= 8))
    
    s.add(Or(oslo_conds))
    s.add(Or(tallinn_conds))
    
    for i in range(8):
        conds = []
        for (a, b) in edges_list:
            conds.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(conds))
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m[order[i]].as_long() for i in range(9)]
        start_days = [1]
        cum = 0
        for i in range(8):
            d_req = days_required[order_vals[i]]
            cum += (d_req - 1)
            start_days.append(1 + cum)
        
        itinerary = []
        for d in range(1, 26):
            for pos in range(9):
                city_idx = order_vals[pos]
                s0 = start_days[pos]
                d_req_city = days_required[city_idx]
                e0 = s0 + d_req_city - 1
                if s0 <= d <= e0:
                    city_name = cities[city_idx]
                    itinerary.append({"day": d, "city": city_name})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()