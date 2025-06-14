from z3 import *

def main():
    # Given input parameters
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
    
    # Segment city variables
    seg_city = [Int(f'seg_city_{i}') for i in range(n_seg)]
    # Start and end day variables for each segment
    s_day = [Int(f's_{i}') for i in range(n_seg)]
    e_day = [Int(f'e_{i}') for i in range(n_seg)]
    # Duration of each segment (travel time)
    dur_seg = [Int(f'dur_seg_{i}') for i in range(n_seg)]
    
    # Create a Z3 array for city durations
    duration_array = Array('durations', IntSort(), IntSort())
    for i in range(n_city):
        s.add(duration_array[i] == dur_all[i])
    
    # Create an uninterpreted function for travel times
    travel_func = Function('travel_func', IntSort(), IntSort(), IntSort())
    for i in range(n_city):
        for j in range(n_city):
            s.add(travel_func(i, j) == travel_time[i][j])
    
    # Constraint: first segment start day is the stay duration at city0
    s.add(s_day[0] == dur_all[0])
    
    # Constraints for each segment
    for i in range(n_seg):
        # Determine previous city: for segment0, it's city0; otherwise, it's the city of the previous segment
        if i == 0:
            prev_city = 0
        else:
            prev_city = seg_city[i-1]
        # Travel time from previous city to current segment city
        s.add(dur_seg[i] == travel_func(prev_city, seg_city[i]))
        # End day is start day plus travel time
        s.add(e_day[i] == s_day[i] + dur_seg[i])
        
    # Constraints connecting segments: for i>=1, start day of segment i is end day of segment i-1 plus stay at seg_city[i-1]
    for i in range(1, n_seg):
        s.add(s_day[i] == e_day[i-1] + Select(duration_array, seg_city[i-1]))
    
    # Last segment must end at city4 (index n_city-1)
    s.add(seg_city[n_seg-1] == n_city-1)
    
    # Arrive at city4 on the last day (day20)
    s.add(e_day[n_seg-1] == n_days - 1)
    
    # Every city from 1 to n_city-1 must appear in seg_city
    for c in range(1, n_city):
        s.add(Or([seg_city[i] == c for i in range(n_seg)]))
    
    # Ensure segment cities are within valid range
    for i in range(n_seg):
        s.add(seg_city[i] >= 0)
        s.add(seg_city[i] < n_city)
    
    # Days must be non-negative and within total days
    for i in range(n_seg):
        s.add(s_day[i] >= 0)
        s.add(e_day[i] >= 0)
        s.add(s_day[i] < n_days)
        s.add(e_day[i] < n_days)
    
    # Check satisfiability and print the model
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
        
        # Print the itinerary day by day
        current_day = 0
        print("\nItinerary:")
        print(f"Day 0: Start at city0 (stay for {dur_all[0]} days, leaving on day {dur_all[0]})")
        current_day = dur_all[0]
        for i in range(n_seg):
            from_city = 0 if i == 0 else seg_city_vals[i-1]
            to_city = seg_city_vals[i]
            print(f"Segment {i}: Travel from city{from_city} to city{to_city} starting on day {s_day_vals[i]} (takes {dur_seg_vals[i]} days), arrives on day {e_day_vals[i]}")
            # For non-last cities, show stay duration
            if i < n_seg - 1:
                print(f"  Stay at city{to_city} for {dur_all[to_city]} days, from day {e_day_vals[i]} to day {e_day_vals[i] + dur_all[to_city] - 1}, leaving on day {e_day_vals[i] + dur_all[to_city]}")
            else:  # Last city (city4)
                print(f"  Stay at city{to_city} for {dur_all[to_city]} day, on day {e_day_vals[i]}")
            current_day = e_day_vals[i] + dur_all[to_city]
        print(f"End at city4 on day {n_days-1}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()