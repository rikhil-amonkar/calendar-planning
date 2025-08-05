from z3 import *
import json

def main():
    cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    name_to_index = {city: idx for idx, city in enumerate(cities)}
    days_req = [2, 2, 5, 3, 4, 3, 3, 2]
    
    flight_pairs = [
        ('Copenhagen', 'Vienna'),
        ('Nice', 'Stockholm'),
        ('Split', 'Copenhagen'),
        ('Nice', 'Reykjavik'),
        ('Nice', 'Porto'),
        ('Reykjavik', 'Vienna'),
        ('Stockholm', 'Copenhagen'),
        ('Nice', 'Venice'),
        ('Nice', 'Vienna'),
        ('Reykjavik', 'Copenhagen'),
        ('Nice', 'Copenhagen'),
        ('Stockholm', 'Vienna'),
        ('Venice', 'Vienna'),
        ('Copenhagen', 'Porto'),
        ('Reykjavik', 'Stockholm'),
        ('Stockholm', 'Split'),
        ('Split', 'Vienna'),
        ('Copenhagen', 'Venice'),
        ('Vienna', 'Porto')
    ]
    
    edges_set = set()
    for a, b in flight_pairs:
        i1 = name_to_index[a]
        i2 = name_to_index[b]
        u, v = (i1, i2) if i1 < i2 else (i2, i1)
        edges_set.add((u, v))
    
    s = Solver()
    
    position = [Int(f'pos_{i}') for i in range(8)]
    for p in position:
        s.add(p >= 0, p <= 7)
    s.add(Distinct(position))
    
    pos_of_city = [Int(f'pos_city_{city}') for city in cities]
    for pc in pos_of_city:
        s.add(pc >= 0, pc <= 7)
    
    for idx in range(8):
        s.add(pos_of_city[position[idx]] == idx)
        s.add(position[pos_of_city[idx]] == idx)
    
    for i in range(7):
        a = position[i]
        b = position[i+1]
        edge_conds = []
        for edge in edges_set:
            u, v = edge
            edge_conds.append(And(a == u, b == v))
            edge_conds.append(And(a == v, b == u))
        s.add(Or(edge_conds))
    
    cum = [Int(f'cum_{i}') for i in range(9)]
    s.add(cum[0] == 1)
    for k in range(8):
        d_k = Int(f'd_{k}')
        s.add(d_k == Sum([If(position[k] == j, days_req[j], 0) for j in range(8)]))
        s.add(cum[k+1] == cum[k] + (d_k - 1))
    
    def get_cum_at(idx, cum_list):
        return If(idx == 0, cum_list[0],
                If(idx == 1, cum_list[1],
                If(idx == 2, cum_list[2],
                If(idx == 3, cum_list[3],
                If(idx == 4, cum_list[4],
                If(idx == 5, cum_list[5],
                If(idx == 6, cum_list[6],
                If(idx == 7, cum_list[7],
                0))))))))
    
    start0 = get_cum_at(pos_of_city[0], cum)
    s.add(start0 <= 4, start0 >= 2)
    
    start1 = get_cum_at(pos_of_city[1], cum)
    s.add(start1 <= 5, start1 >= 3)
    
    start2 = get_cum_at(pos_of_city[2], cum)
    s.add(start2 + 4 >= 13, start2 <= 17)
    
    start5 = get_cum_at(pos_of_city[5], cum)
    s.add(start5 + 2 >= 11, start5 <= 13)
    
    if s.check() == sat:
        model = s.model()
        seq = [model.eval(position[i]).as_long() for i in range(8)]
        starts = [1]
        ends = []
        for i in range(8):
            dur = days_req[seq[i]]
            end_day = starts[i] + dur - 1
            ends.append(end_day)
            if i < 7:
                starts.append(end_day)
        
        itinerary_list = []
        for day in range(1, 18):
            places = []
            for i in range(8):
                if starts[i] <= day <= ends[i]:
                    places.append(cities[seq[i]])
            itinerary_list.append({"day": day, "place": ", ".join(places)})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()