from z3 import *

def main():
    city_to_index = {
        "Krakow": 0,
        "Frankfurt": 1,
        "Oslo": 2,
        "Dubrovnik": 3,
        "Naples": 4
    }
    index_to_city = {v: k for k, v in city_to_index.items()}
    durations_list = [5, 4, 3, 5, 5]  # Krakow, Frankfurt, Oslo, Dubrovnik, Naples

    direct_flights = [
        ("Dubrovnik", "Oslo"),
        ("Frankfurt", "Krakow"),
        ("Frankfurt", "Oslo"),
        ("Dubrovnik", "Frankfurt"),
        ("Krakow", "Oslo"),
        ("Naples", "Oslo"),
        ("Naples", "Dubrovnik"),
        ("Naples", "Frankfurt")
    ]
    allowed_pairs_set = set()
    for a, b in direct_flights:
        i = city_to_index[a]
        j = city_to_index[b]
        key = (min(i, j), max(i, j))
        allowed_pairs_set.add(key)

    s = Solver()

    order = [Int(f'o_{i}') for i in range(5)]
    for i in range(5):
        s.add(order[i] >= 0, order[i] <= 4)
    s.add(Distinct(order))

    starts = [Int(f'start_{i}') for i in range(5)]
    ends = [Int(f'end_{i}') for i in range(5)]

    s.add(starts[0] == 1)
    
    def get_dur(idx):
        return If(idx == 0, durations_list[0],
                If(idx == 1, durations_list[1],
                If(idx == 2, durations_list[2],
                If(idx == 3, durations_list[3], durations_list[4]))))
    
    for i in range(5):
        dur_i = get_dur(order[i])
        s.add(ends[i] == starts[i] + dur_i - 1)
        if i < 4:
            s.add(starts[i+1] == ends[i])
    
    s.add(ends[4] == 18)
    
    for i in range(5):
        s.add(If(order[i] == 3, starts[i] <= 9, True))
        s.add(If(order[i] == 2, And(starts[i] >= 14, starts[i] <= 16), True))
    
    for i in range(4):
        a = order[i]
        b = order[i+1]
        low = If(a < b, a, b)
        high = If(a < b, b, a)
        cond = False
        for pair in allowed_pairs_set:
            cond = Or(cond, And(low == pair[0], high == pair[1]))
        s.add(cond)
    
    if s.check() == sat:
        model = s.model()
        order_vals = [model.evaluate(order[i]).as_long() for i in range(5)]
        start_vals = [model.evaluate(starts[i]).as_long() for i in range(5)]
        end_vals = [model.evaluate(ends[i]).as_long() for i in range(5)]
        
        itinerary = []
        for day in range(1, 19):
            for seg in range(5):
                s_val = start_vals[seg]
                e_val = end_vals[seg]
                if s_val <= day <= e_val:
                    city_idx = order_vals[seg]
                    city_name = index_to_city[city_idx]
                    itinerary.append({"day": day, "place": city_name})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()