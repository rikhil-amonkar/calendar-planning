from z3 import *

def main():
    n_city = 5
    n_seg = 4
    n_days = 21
    dur_all = [0, 1, 1, 1, 1]
    travel_time = [
        [0, 1, 2, 3, 4],
        [1, 0, 1, 2, 3],
        [2, 1, 0, 1, 2],
        [3, 2, 1, 0, 1],
        [4, 3, 2, 1, 0]
    ]
    
    s = Solver()
    
    seg_city = [Int(f'seg_city_{i}') for i in range(n_seg)]
    s_day = [Int(f's_{i}') for i in range(n_seg)]
    e_day = [Int(f'e_{i}') for i in range(n_seg)]
    dur_seg = [Int(f'dur_seg_{i}') for i in range(n_seg)]
    
    duration_array = Array('durations', IntSort(), IntSort())
    for i in range(n_city):
        s.add(duration_array[i] == dur_all[i])
    
    travel_func = Function('travel_func', IntSort(), IntSort(), IntSort())
    for i in range(n_city):
        for j in range(n_city):
            s.add(travel_func(i, j) == travel_time[i][j])
    
    s.add(s_day[0] == dur_all[0])
    
    for i in range(n_seg):
        prev_city = 0 if i == 0 else seg_city[i-1]
        s.add(dur_seg[i] == travel_func(prev_city, seg_city[i]))
        s.add(e_day[i] == s_day[i] + dur_seg[i])
        
    for i in range(1, n_seg):
        s.add(s_day[i] == e_day[i-1] + Select(duration_array, seg_city[i-1]))
    
    s.add(seg_city[n_seg-1] == n_city-1)
    s.add(e_day[n_seg-1] == n_days - 1)
    
    for c in range(1, n_city):
        s.add(Or([seg_city[i] == c for i in range(n_seg)]))
    
    for i in range(n_seg):
        s.add(And(seg_city[i] >= 0, seg_city[i] < n_city))
        s.add(And(s_day[i] >= 0, s_day[i] < n_days))
        s.add(And(e_day[i] >= 0, e_day[i] < n_days))
    
    if s.check() == sat:
        m = s.model()
        print("Solution found:")
        seg_city_vals = [m.evaluate(seg_city[i]).as_long() for i in range(n_seg)]
        s_day_vals = [m.evaluate(s_day[i]).as_long() for i in range(n_seg)]
        e_day_vals = [m.evaluate(e_day[i]).as_long() for i in range(n_seg)]
        dur_seg_vals = [m.evaluate(dur_seg[i]).as_long() for i in range(n_seg)]
        
        print("Segment cities:", seg_city_vals)
        print("Start days:", s_day_vals)
        print("End days:", e_day_vals)
        print("Durations (travel):", dur_seg_vals)
        
        print("\nItinerary:")
        print(f"Day 0: Start at city0 (stay for 0 days, leaving on day 0)")
        for i in range(n_seg):
            from_city = 0 if i == 0 else seg_city_vals[i-1]
            to_city = seg_city_vals[i]
            print(f"Segment {i}: Travel from city{from_city} to city{to_city} starting on day {s_day_vals[i]} (takes {dur_seg_vals[i]} days), arrives on day {e_day_vals[i]}")
            if i < n_seg - 1:
                print(f"  Stay at city{to_city} for {dur_all[to_city]} days, from day {e_day_vals[i]} to day {e_day_vals[i]}, leaving on day {e_day_vals[i] + dur_all[to_city]}")
        print(f"  Stay at city4 for 1 day on day {e_day_vals[3]}")
        print(f"End at city4 on day {n_days-1}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()