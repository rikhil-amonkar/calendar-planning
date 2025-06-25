from z3 import *

def main():
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    days_arr = [4, 3, 3, 3, 4, 4, 2]
    directed_edges = [
        (0, 3), (3, 5),  # Directed: Rome->Riga, Riga->Munich
        (0, 1), (1, 0),  # Rome <-> Mykonos
        (0, 2), (2, 0),  # Rome <-> Nice
        (0, 4), (4, 0),  # Rome <-> Bucharest
        (0, 5), (5, 0),  # Rome <-> Munich
        (1, 5), (5, 1),  # Mykonos <-> Munich
        (1, 2), (2, 1),  # Mykonos <-> Nice
        (3, 2), (2, 3),  # Riga <-> Nice
        (3, 4), (4, 3),  # Riga <-> Bucharest
        (4, 5), (5, 4),  # Bucharest <-> Munich
        (2, 5), (5, 2),  # Nice <-> Munich
        (5, 6), (6, 5)   # Munich <-> Krakow
    ]
    
    s = Solver()
    o1, o2, o3, o4, o5 = Ints('o1 o2 o3 o4 o5')
    order = [0, o1, o2, o3, o4, o5, 6]
    
    s.add(Distinct(o1, o2, o3, o4, o5))
    for o in [o1, o2, o3, o4, o5]:
        s.add(And(o >= 1, o <= 5))
    
    days_z3 = Array('days_z3', IntSort(), IntSort())
    for idx, d_val in enumerate(days_arr):
        s.add(days_z3[idx] == d_val)
    
    d0 = 4
    d1 = d0 + days_z3[o1] - 1
    d2 = d1 + days_z3[o2] - 1
    d3 = d2 + days_z3[o3] - 1
    d4 = d3 + days_z3[o4] - 1
    d5 = d4 + days_z3[o5] - 1
    s.add(d5 == 16)
    
    mykonos_idx = 1
    s.add(Or(o1 == mykonos_idx, o2 == mykonos_idx, o3 == mykonos_idx))
    s.add(If(o1 == mykonos_idx, True,
             If(o2 == mykonos_idx, d1 <= 6,
                If(o3 == mykonos_idx, d2 <= 6, False))))
    
    for i in range(6):
        from_city = order[i]
        to_city = order[i+1]
        edge_constraints = []
        for u, v in directed_edges:
            edge_constraints.append(And(from_city == u, to_city == v))
        s.add(Or(edge_constraints))
    
    if s.check() == sat:
        m = s.model()
        o1_val = m[o1].as_long()
        o2_val = m[o2].as_long()
        o3_val = m[o3].as_long()
        o4_val = m[o4].as_long()
        o5_val = m[o5].as_long()
        full_order = [0, o1_val, o2_val, o3_val, o4_val, o5_val, 6]
        
        d_vals = [4]  # d0
        for i in range(1, 6):
            d_vals.append(d_vals[i-1] + days_arr[full_order[i]] - 1)
        
        arrival = [1]
        for i in range(1, 7):
            arrival.append(d_vals[i-1])
        
        itinerary = []
        for i in range(7):
            city = cities[full_order[i]]
            a = arrival[i]
            b = d_vals[i] if i < 6 else 17
            
            if a == b:
                itinerary.append({"day_range": f"Day {a}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {a}-{b}", "place": city})
            
            if i < 6:
                next_city = cities[full_order[i+1]]
                itinerary.append({"day_range": f"Day {b}", "place": city})
                itinerary.append({"day_range": f"Day {b}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()