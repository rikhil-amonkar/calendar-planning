from z3 import *

def main():
    # Cities with their durations and fixed intervals where applicable
    cities = {
        "Madrid": (4, 1, 4),       # 4 days, fixed days 1-4
        "Stuttgart": (7, 7, 13),    # 7 days, fixed days 7-13
        "Seville": (2, None, None), # 2 days, flexible
        "Porto": (3, None, None)    # 3 days, flexible
    }
    
    # Direct flight connections (bidirectional)
    connections = [
        ("Porto", "Stuttgart"),
        ("Seville", "Porto"),
        ("Madrid", "Porto"),
        ("Madrid", "Seville")
    ]
    
    s = Solver()
    
    # Variables for flexible cities' start and end days
    flex_vars = {}
    for city in cities:
        if cities[city][1] is None:
            duration = cities[city][0]
            start = Int(f"{city}_start")
            end = Int(f"{city}_end")
            s.add(start >= 1, end == start + duration - 1, end <= 13)
            flex_vars[city] = (start, end)
        else:
            flex_vars[city] = (cities[city][1], cities[city][2])
    
    # Collect all intervals
    intervals = []
    for city in cities:
        start, end = flex_vars[city]
        intervals.append((start, end, city))
    
    # Ensure no overlapping intervals
    for i in range(len(intervals)):
        s_i_start, s_i_end, city_i = intervals[i]
        for j in range(i+1, len(intervals)):
            s_j_start, s_j_end, city_j = intervals[j]
            s.add(Or(s_i_end < s_j_start, s_j_end < s_i_start))
    
    # Ensure all days 1-13 are covered
    days = [Bool(f"day_{d}") for d in range(1, 14)]
    for d in range(1, 14):
        day_covered = Or(*[And(s_i_start <= d, d <= s_i_end) for (s_i_start, s_i_end, _) in intervals])
        s.add(day_covered)
    
    # Ensure flight connections between consecutive cities in schedule order
    city_order = sorted(intervals, key=lambda x: x[0])
    for i in range(len(city_order) - 1):
        current_city = city_order[i][2]
        next_city = city_order[i+1][2]
        s.add(Or(
            (current_city, next_city) in connections,
            (next_city, current_city) in connections
        ))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for city in cities:
            if cities[city][1] is None:
                start = m[flex_vars[city][0]].as_long()
                end = m[flex_vars[city][1]].as_long()
            else:
                start, end = cities[city][1], cities[city][2]
            schedule.append((start, end, city))
        schedule.sort()
        print("Valid Trip Plan:")
        for start, end, city in schedule:
            print(f"{city}: Days {start}-{end}")
    else:
        print("No valid trip plan found")

if __name__ == "__main__":
    main()