from z3 import *

def main():
    s = Solver()
    
    cities = ["Oslo", "Helsinki", "Edinburgh", "Riga", "Tallinn", "Budapest", "Vilnius", "Porto", "Geneva"]
    durations = [2, 2, 3, 2, 5, 5, 5, 5, 4]
    
    graph = [[False] * 9 for _ in range(9)]
    
    def add_edge(u, v):
        graph[u][v] = True
        graph[v][u] = True
        
    def add_directed_edge(u, v):
        graph[u][v] = True
        
    add_edge(7, 0)  # Porto and Oslo
    add_edge(2, 5)  # Edinburgh and Budapest
    add_edge(2, 8)  # Edinburgh and Geneva
    add_directed_edge(3, 4)  # Riga to Tallinn
    add_edge(2, 7)  # Edinburgh and Porto
    add_edge(6, 1)  # Vilnius and Helsinki
    add_directed_edge(4, 6)  # Tallinn to Vilnius
    add_edge(3, 0)  # Riga and Oslo
    add_edge(8, 0)  # Geneva and Oslo
    add_edge(2, 0)  # Edinburgh and Oslo
    add_edge(2, 1)  # Edinburgh and Helsinki
    add_edge(6, 0)  # Vilnius and Oslo
    add_edge(3, 1)  # Riga and Helsinki
    add_edge(5, 8)  # Budapest and Geneva
    add_edge(1, 5)  # Helsinki and Budapest
    add_edge(1, 0)  # Helsinki and Oslo
    add_edge(2, 3)  # Edinburgh and Riga
    add_edge(4, 1)  # Tallinn and Helsinki
    add_edge(8, 7)  # Geneva and Porto
    add_edge(5, 0)  # Budapest and Oslo
    add_edge(1, 8)  # Helsinki and Geneva
    add_directed_edge(3, 6)  # Riga to Vilnius
    add_edge(4, 0)  # Tallinn and Oslo
    
    order = [Int(f'order_{i}') for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    for i in range(8):
        conditions = []
        for u in range(9):
            for v in range(9):
                if graph[u][v]:
                    conditions.append(And(order[i] == u, order[i+1] == v))
        s.add(Or(conditions))
    
    dur_arr = Array('dur_arr', IntSort(), IntSort())
    for idx in range(9):
        s.add(dur_arr[idx] == durations[idx])
    
    pos4 = Int('pos4')
    s.add(Or([And(order[j] == 4, pos4 == j) for j in range(9)]))
    start4 = 1 + Sum([If(j < pos4, dur_arr[order[j]] - 1, 0) for j in range(9)])
    s.add(start4 == 4)
    
    pos0 = Int('pos0')
    s.add(Or([And(order[j] == 0, pos0 == j) for j in range(9)]))
    start0 = 1 + Sum([If(j < pos0, dur_arr[order[j]] - 1, 0) for j in range(9)])
    end0 = start0 + dur_arr[0] - 1
    s.add(Or(start0 == 24, start0 == 23, end0 == 24, end0 == 25))
    
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