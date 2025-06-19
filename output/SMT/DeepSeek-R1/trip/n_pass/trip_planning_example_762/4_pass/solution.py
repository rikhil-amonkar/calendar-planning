from z3 import *

def main():
    dublin = 0
    madrid = 1
    oslo = 2
    london = 3
    vilnius = 4
    berlin = 5

    cities = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]
    dur = [3, 2, 3, 2, 3, 5]

    undir_edges = [
        (london, madrid),
        (oslo, vilnius),
        (berlin, vilnius),
        (madrid, oslo),
        (madrid, dublin),
        (london, oslo),
        (madrid, berlin),
        (berlin, oslo),
        (dublin, oslo),
        (london, dublin),
        (london, berlin),
        (berlin, dublin)
    ]
    
    edges = []
    for u, v in undir_edges:
        edges.append((u, v))
        edges.append((v, u))
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(6)]
    for i in range(6):
        s.add(order[i] >= 0, order[i] < 6)
    s.add(Distinct(order))
    
    for i in range(5):
        valid_edges = []
        for u, v in edges:
            valid_edges.append(And(order[i] == u, order[i+1] == v))
        s.add(Or(valid_edges))
    
    dur_array = Array('durations', IntSort(), IntSort())
    for i in range(6):
        s.add(dur_array[i] == dur[i])
    
    seq_start = [Int(f'seq_start_{i}') for i in range(6)]
    s.add(seq_start[0] == 1)
    
    for i in range(1, 6):
        prev_dur = Select(dur_array, order[i-1])
        s.add(seq_start[i] == seq_start[i-1] + prev_dur - 1)
    
    for i in range(6):
        city = order[i]
        s.add(If(city == dublin, And(seq_start[i] >= 5, seq_start[i] <= 9), True))
        s.add(If(city == madrid, seq_start[i] == 2, True))
        s.add(If(city == berlin, seq_start[i] <= 7, True))
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(6)]
        seq_start_vals = [m.evaluate(seq_start[i]).as_long() for i in range(6)]
        
        itinerary = []
        for i in range(6):
            city_idx = order_vals[i]
            s_day = seq_start_vals[i]
            e_day = s_day + dur[city_idx] - 1
            itinerary.append({"day_range": f"Day {s_day}-{e_day}", "place": cities[city_idx]})
            if i < 5:
                itinerary.append({"day_range": f"Day {e_day}", "place": cities[city_idx]})
                next_city_idx = order_vals[i+1]
                itinerary.append({"day_range": f"Day {e_day}", "place": cities[next_city_idx]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()