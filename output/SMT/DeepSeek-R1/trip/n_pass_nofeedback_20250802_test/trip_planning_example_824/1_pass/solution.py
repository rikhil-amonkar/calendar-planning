from z3 import *
import json

def main():
    cities = ['Berlin', 'Split', 'Bucharest', 'Riga', 'Lisbon', 'Tallinn', 'Lyon']
    reqs = [5, 3, 3, 5, 3, 4, 5]
    n = len(cities)
    
    adj = [
        [0, 1, 0, 1, 1, 1, 0],   # Berlin:0
        [1, 0, 0, 0, 0, 0, 1],    # Split:1
        [0, 0, 0, 1, 1, 0, 1],    # Bucharest:2
        [1, 0, 1, 0, 1, 1, 0],    # Riga:3
        [1, 0, 1, 1, 0, 0, 1],    # Lisbon:4
        [1, 0, 0, 0, 0, 0, 0],    # Tallinn:5
        [0, 1, 1, 0, 1, 0, 0]     # Lyon:6
    ]
    
    Order = IntVector('Order', n)
    s = Solver()
    
    for i in range(n):
        s.add(Order[i] >= 0, Order[i] < n)
    
    s.add(Distinct(Order))
    
    for i in range(n):
        prefix_sum_i = Sum([If(j < i, reqs[Order[j]], 0) for j in range(n)])
        s.add(If(Order[i] == 0, prefix_sum_i == i, True))
        s.add(If(Order[i] == 6, prefix_sum_i == 6 + i, True))
        s.add(If(Order[i] == 2, prefix_sum_i == 12 + i, True))
    
    for i in range(n-1):
        s.add(adj[Order[i]][Order[i+1]] == 1)
    
    if s.check() == sat:
        m = s.model()
        order_list = [m[Order[i]].as_long() for i in range(n)]
        
        prefix = 0
        starts = [0] * n
        ends = [0] * n
        
        for i in range(n):
            city_index = order_list[i]
            start_i = 1 + prefix - i
            end_i = start_i + reqs[city_index] - 1
            starts[city_index] = start_i
            ends[city_index] = end_i
            prefix += reqs[city_index]
        
        itinerary = []
        for day in range(1, 23):
            for idx in range(n):
                if starts[idx] <= day <= ends[idx]:
                    itinerary.append({"day": day, "place": cities[idx]})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()