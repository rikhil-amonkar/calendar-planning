from z3 import *

def main():
    # Cities with their durations and fixed intervals
    cities = {
        "Stockholm": (3, None, None),
        "Hamburg": (5, None, None),
        "Florence": (2, None, None),
        "Istanbul": (5, 25, 29),
        "Oslo": (5, None, None),
        "Vilnius": (5, None, None),
        "Santorini": (2, None, None),
        "Munich": (5, None, None),
        "Frankfurt": (4, None, None),
        "Krakow": (5, 5, 9),
    }
    
    # Direct flight connections (directional)
    connections = [
        ("Oslo", "Stockholm"), ("Stockholm", "Oslo"),
        ("Krakow", "Frankfurt"), ("Frankfurt", "Krakow"),
        ("Krakow", "Istanbul"), ("Istanbul", "Krakow"),
        ("Munich", "Stockholm"), ("Stockholm", "Munich"),
        ("Hamburg", "Stockholm"), ("Stockholm", "Hamburg"),
        ("Krakow", "Vilnius"),
        ("Oslo", "Istanbul"), ("Istanbul", "Oslo"),
        ("Istanbul", "Stockholm"), ("Stockholm", "Istanbul"),
        ("Oslo", "Krakow"), ("Krakow", "Oslo"),
        ("Vilnius", "Istanbul"), ("Istanbul", "Vilnius"),
        ("Oslo", "Vilnius"), ("Vilnius", "Oslo"),
        ("Frankfurt", "Istanbul"), ("Istanbul", "Frankfurt"),
        ("Oslo", "Frankfurt"), ("Frankfurt", "Oslo"),
        ("Munich", "Hamburg"), ("Hamburg", "Munich"),
        ("Munich", "Istanbul"), ("Istanbul", "Munich"),
        ("Oslo", "Munich"), ("Munich", "Oslo"),
        ("Frankfurt", "Florence"), ("Florence", "Frankfurt"),
        ("Oslo", "Hamburg"), ("Hamburg", "Oslo"),
        ("Vilnius", "Frankfurt"), ("Frankfurt", "Vilnius"),
        ("Florence", "Munich"),
        ("Krakow", "Munich"), ("Munich", "Krakow"),
        ("Hamburg", "Istanbul"), ("Istanbul", "Hamburg"),
        ("Frankfurt", "Stockholm"), ("Stockholm", "Frankfurt"),
        ("Stockholm", "Santorini"),
        ("Frankfurt", "Munich"), ("Munich", "Frankfurt"),
        ("Santorini", "Oslo"),
        ("Krakow", "Stockholm"), ("Stockholm", "Krakow"),
        ("Vilnius", "Munich"),
        ("Frankfurt", "Hamburg"), ("Hamburg", "Frankfurt"),
    ]
    
    s = Solver()
    
    # Variables for flexible cities' start and end days
    flex_vars = {}
    for city in cities:
        if cities[city][1] is None:
            duration = cities[city][0]
            start = Int(f"{city}_start")
            end = Int(f"{city}_end")
            s.add(start >= 1, end == start + duration - 1, end <= 32)
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
        for j in range(i + 1, len(intervals)):
            s_j_start, s_j_end, city_j = intervals[j]
            s.add(Or(s_i_end < s_j_start, s_j_end < s_i_start))
    
    # Ensure all days 1-32 are covered
    for d in range(1, 33):
        day_covered = Or([And(s_i_start <= d, d <= s_i_end) for (s_i_start, s_i_end, _) in intervals])
        s.add(day_covered)
    
    # Ensure consecutive cities are connected by flights (directional check)
    city_order = sorted(intervals, key=lambda x: x[0])
    for i in range(len(city_order) - 1):
        current_city = city_order[i][2]
        next_city = city_order[i+1][2]
        s.add((current_city, next_city) in connections)
    
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