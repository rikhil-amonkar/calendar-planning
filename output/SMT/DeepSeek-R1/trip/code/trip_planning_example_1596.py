from z3 import *

def main():
    # Cities with their durations and fixed intervals
    cities = {
        "Edinburgh": (5, 1, 5),
        "Budapest": (5, 9, 13),
        "Stockholm": (2, 17, 18),
        "Munich": (3, 18, 20),
        "Warsaw": (5, 25, 29),
        "Bucharest": (2, None, None),
        "Krakow": (4, None, None),
        "Barcelona": (5, None, None),
        "Riga": (5, None, None),
        "Vienna": (5, None, None),
    }
    
    # Direct flight connections (directional)
    connections = [
        ("Budapest", "Munich"), ("Munich", "Budapest"),
        ("Bucharest", "Riga"), ("Riga", "Bucharest"),
        ("Munich", "Krakow"), ("Krakow", "Munich"),
        ("Munich", "Warsaw"), ("Warsaw", "Munich"),
        ("Munich", "Bucharest"), ("Bucharest", "Munich"),
        ("Edinburgh", "Stockholm"), ("Stockholm", "Edinburgh"),
        ("Barcelona", "Warsaw"), ("Warsaw", "Barcelona"),
        ("Edinburgh", "Krakow"), ("Krakow", "Edinburgh"),
        ("Barcelona", "Munich"), ("Munich", "Barcelona"),
        ("Stockholm", "Krakow"), ("Krakow", "Stockholm"),
        ("Budapest", "Vienna"), ("Vienna", "Budapest"),
        ("Barcelona", "Stockholm"), ("Stockholm", "Barcelona"),
        ("Stockholm", "Munich"), ("Munich", "Stockholm"),
        ("Edinburgh", "Budapest"), ("Budapest", "Edinburgh"),
        ("Barcelona", "Riga"), ("Riga", "Barcelona"),
        ("Edinburgh", "Barcelona"), ("Barcelona", "Edinburgh"),
        ("Vienna", "Riga"), ("Riga", "Vienna"),
        ("Barcelona", "Budapest"), ("Budapest", "Barcelona"),
        ("Bucharest", "Warsaw"), ("Warsaw", "Bucharest"),
        ("Vienna", "Krakow"), ("Krakow", "Vienna"),
        ("Edinburgh", "Munich"), ("Munich", "Edinburgh"),
        ("Barcelona", "Bucharest"), ("Bucharest", "Barcelona"),
        ("Edinburgh", "Riga"), ("Riga", "Edinburgh"),
        ("Vienna", "Stockholm"), ("Stockholm", "Vienna"),
        ("Warsaw", "Krakow"), ("Krakow", "Warsaw"),
        ("Barcelona", "Krakow"), ("Krakow", "Barcelona"),
        ("Riga", "Munich"),
        ("Vienna", "Bucharest"), ("Bucharest", "Vienna"),
        ("Budapest", "Warsaw"), ("Warsaw", "Budapest"),
        ("Vienna", "Warsaw"), ("Warsaw", "Vienna"),
        ("Barcelona", "Vienna"), ("Vienna", "Barcelona"),
        ("Budapest", "Bucharest"), ("Bucharest", "Budapest"),
        ("Vienna", "Munich"), ("Munich", "Vienna"),
        ("Riga", "Warsaw"), ("Warsaw", "Riga"),
        ("Stockholm", "Riga"), ("Riga", "Stockholm"),
        ("Stockholm", "Warsaw"), ("Warsaw", "Stockholm"),
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