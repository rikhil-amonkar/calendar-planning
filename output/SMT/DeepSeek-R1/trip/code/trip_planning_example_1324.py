from z3 import *

def main():
    # Cities with their durations and fixed intervals
    cities = {
        "Barcelona": (3, 10, 12),
        "Copenhagen": (4, 7, 10),
        "Dubrovnik": (5, 16, 20),
        "Venice": (4, None, None),
        "Lyon": (4, None, None),
        "Reykjavik": (4, None, None),
        "Athens": (2, None, None),
        "Tallinn": (5, None, None),
        "Munich": (3, None, None),
    }
    
    # Direct flight connections (directional)
    connections = [
        ("Copenhagen", "Athens"), ("Athens", "Copenhagen"),
        ("Copenhagen", "Dubrovnik"), ("Dubrovnik", "Copenhagen"),
        ("Munich", "Tallinn"), ("Tallinn", "Munich"),
        ("Copenhagen", "Munich"), ("Munich", "Copenhagen"),
        ("Venice", "Munich"), ("Munich", "Venice"),
        ("Reykjavik", "Athens"),  # One-way from Reykjavik to Athens
        ("Athens", "Dubrovnik"), ("Dubrovnik", "Athens"),
        ("Venice", "Athens"), ("Athens", "Venice"),
        ("Lyon", "Barcelona"), ("Barcelona", "Lyon"),
        ("Copenhagen", "Reykjavik"), ("Reykjavik", "Copenhagen"),
        ("Reykjavik", "Munich"), ("Munich", "Reykjavik"),
        ("Athens", "Munich"), ("Munich", "Athens"),
        ("Lyon", "Munich"), ("Munich", "Lyon"),
        ("Barcelona", "Reykjavik"), ("Reykjavik", "Barcelona"),
        ("Venice", "Copenhagen"), ("Copenhagen", "Venice"),
        ("Barcelona", "Dubrovnik"), ("Dubrovnik", "Barcelona"),
        ("Lyon", "Venice"), ("Venice", "Lyon"),
        ("Dubrovnik", "Munich"), ("Munich", "Dubrovnik"),
        ("Barcelona", "Athens"), ("Athens", "Barcelona"),
        ("Copenhagen", "Barcelona"), ("Barcelona", "Copenhagen"),
        ("Venice", "Barcelona"), ("Barcelona", "Venice"),
        ("Barcelona", "Munich"), ("Munich", "Barcelona"),
        ("Barcelona", "Tallinn"), ("Tallinn", "Barcelona"),
        ("Copenhagen", "Tallinn"), ("Tallinn", "Copenhagen"),
    ]
    
    s = Solver()
    
    # Variables for flexible cities' start and end days
    flex_vars = {}
    for city in cities:
        if cities[city][1] is None:
            duration = cities[city][0]
            start = Int(f"{city}_start")
            end = Int(f"{city}_end")
            s.add(start >= 1, end == start + duration - 1, end <= 26)
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
    
    # Ensure all days 1-26 are covered
    for d in range(1, 27):
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