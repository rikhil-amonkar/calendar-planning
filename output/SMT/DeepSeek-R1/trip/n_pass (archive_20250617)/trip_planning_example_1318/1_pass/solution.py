from z3 import *

def main():
    s = Solver()
    
    cities = ["Oslo", "Helsinki", "Edinburgh", "Riga", "Tallinn", "Budapest", "Vilnius", "Porto", "Geneva"]
    durations = [2, 2, 3, 2, 5, 5, 5, 5, 4]
    
    graph = [[False] * 9 for _ in range(9)]
    
    def add_edge(u, v):
        graph[u][v] = True
    
    add_edge(7, 0); add_edge(0, 7)
    add_edge(2, 5); add_edge(5, 2)
    add_edge(2, 8); add_edge(8, 2)
    add_edge(3, 4)
    add_edge(2, 7); add_edge(7, 2)
    add_edge(6, 1); add_edge(1, 6)
    add_edge(4, 6)
    add_edge(3, 0); add_edge(0, 3)
    add_edge(8, 0); add_edge(0, 8)
    add_edge(2, 0); add_edge(0, 2)
    add_edge(2, 1); add_edge(1, 2)
    add_edge(6, 0); add_edge(0, 6)
    add_edge(3, 1); add_edge(1, 3)
    add_edge(5, 8); add_edge(8, 5)
    add_edge(1, 5); add_edge(5, 1)
    add_edge(1, 0); add_edge(0, 1)
    add_edge(2, 3); add_edge(3, 2)
    add_edge(4, 1); add_edge(1, 4)
    add_edge(8, 7); add_edge(7, 8)
    add_edge(5, 0); add_edge(0, 5)
    add_edge(1, 8); add_edge(8, 1)
    add_edge(3, 6)
    add_edge(4, 0); add_edge(0, 4)
    
    order = [Int(f'order_{i}') for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    for i in range(8):
        edge_exists = False
        conditions = []
        for u in range(9):
            for v in range(9):
                if graph[u][v]:
                    conditions.append(And(order[i] == u, order[i+1] == v))
        s.add(Or(conditions))
    
    dur_arr = Array('dur_arr', IntSort(), IntSort())
    for idx in range(9):
        s.add(dur_arr[idx] == durations[idx])
    
    pos0 = Int('pos0')
    s.add(Or([And(order[j] == 0, pos0 == j) for j in range(9)]))
    start0 = 1 + Sum([If(j < pos0, dur_arr[order[j]] - 1, 0) for j in range(9)])
    s.add(Or(start0 == 23, start0 == 24))
    
    pos4 = Int('pos4')
    s.add(Or([And(order[j] == 4, pos4 == j) for j in range(9)]))
    start4 = 1 + Sum([If(j < pos4, dur_arr[order[j]] - 1, 0) for j in range(9)])
    s.add(start4 <= 8)
    
    if s.check() == sat:
        m = s.model()
        ord_val = [m.evaluate(order[i]).as_long() for i in range(9)]
        current_start = 1
        for i in range(9):
            city_idx = ord_val[i]
            dur = durations[city_idx]
            end_day = current_start + dur - 1
            print(f"City: {cities[city_idx]}, Start day: {current_start}, End day: {end_day}")
            current_start = end_day
    else:
        print("No solution found")

if __name__ == '__main__':
    main()