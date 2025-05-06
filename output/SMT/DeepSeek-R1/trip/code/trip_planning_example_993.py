from z3 import *

def main():
    # Cities with their durations and fixed intervals
    cities = {
        "Amsterdam": (2, 2, 3),
        "Vilnius": (5, 7, 11),
        "Stockholm": (3, 13, 15),
        "Riga": (2, None, None),
        "Frankfurt": (3, None, None),
        "London": (2, None, None),
        "Bucharest": (4, None, None),
    }
    
    # Direct flights (including directed flights)
    connections = [
        ("London", "Amsterdam"),
        ("Amsterdam", "London"),
        ("Vilnius", "Frankfurt"),
        ("Frankfurt", "Vilnius"),
        ("Riga", "Vilnius"),  # Directed flight
        ("Riga", "Stockholm"),
        ("Stockholm", "Riga"),
        ("London", "Bucharest"),
        ("Bucharest", "London"),
        ("Amsterdam", "Stockholm"),
        ("Stockholm", "Amsterdam"),
        ("Amsterdam", "Frankfurt"),
        ("Frankfurt", "Amsterdam"),
        ("Frankfurt", "Stockholm"),
        ("Stockholm", "Frankfurt"),
        ("Bucharest", "Riga"),
        ("Riga", "Bucharest"),
        ("Amsterdam", "Riga"),
        ("Riga", "Amsterdam"),
        ("Amsterdam", "Bucharest"),
        ("Bucharest", "Amsterdam"),
        ("Riga", "Frankfurt"),
        ("Frankfurt", "Riga"),
        ("Bucharest", "Frankfurt"),
        ("Frankfurt", "Bucharest"),
        ("London", "Frankfurt"),
        ("Frankfurt", "London"),
        ("London", "Stockholm"),
        ("Stockholm", "London"),
        ("Amsterdam", "Vilnius"),
        ("Vilnius", "Amsterdam"),
    ]
    
    s = Solver()
    
    # Variables for flexible cities' start and end days
    flex_vars = {}
    for city in cities:
        if cities[city][1] is None:
            duration = cities[city][0]
            start = Int(f"{city}_start")
            end = Int(f"{city}_end")
            s.add(start >= 1, end == start + duration - 1, end <= 15)
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
    
    # Ensure all days 1-15 are covered
    days = [Bool(f"day_{d}") for d in range(1, 16)]
    for d in range(1, 16):
        day_covered = Or([And(s_i_start <= d, d <= s_i_end) for (s_i_start, s_i_end, _) in intervals])
        s.add(day_covered)
    
    # Ensure consecutive cities are connected by flights
    for city_i in cities:
        for city_j in cities:
            if city_i == city_j:
                continue
            # Get start of j and end of i
            if cities[city_i][1] is None:
                end_i = flex_vars[city_i][1]
            else:
                end_i = cities[city_i][2]
            if cities[city_j][1] is None:
                start_j = flex_vars[city_j][0]
            else:
                start_j = cities[city_j][1]
            # Check if (city_i, city_j) is in connections
            has_flight = (city_i, city_j) in connections
            # If no flight, enforce that j cannot start right after i
            if not has_flight:
                s.add(Not(And(start_j == end_i + 1)))
    
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