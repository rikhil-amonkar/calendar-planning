from z3 import *

def main():
    # Cities and their durations
    cities = {
        "Valencia": (2, 3, 4),      # 2 days, start=3, end=4
        "Seville": (5, 5, 9),       # 5 days, start=5, end=9
        "Oslo": (3, 13, 15),        # 3 days, start=13, end=15
        "Mykonos": (5, 21, 25),     # 5 days, start=21, end=25
        "Lyon": (4, None, None),
        "Prague": (3, None, None),
        "Paris": (4, None, None),
        "Nice": (4, None, None),
        "Tallinn": (2, None, None),
        "Lisbon": (2, None, None),
    }
    
    # Direct flight connections (bidirectional)
    connections = [
        ("Lisbon", "Paris"), ("Lyon", "Nice"), ("Tallinn", "Oslo"), ("Prague", "Lyon"),
        ("Paris", "Oslo"), ("Lisbon", "Seville"), ("Prague", "Lisbon"), ("Oslo", "Nice"),
        ("Valencia", "Paris"), ("Valencia", "Lisbon"), ("Paris", "Nice"), ("Nice", "Mykonos"),
        ("Paris", "Lyon"), ("Valencia", "Lyon"), ("Prague", "Oslo"), ("Prague", "Paris"),
        ("Seville", "Paris"), ("Oslo", "Lyon"), ("Prague", "Valencia"), ("Lisbon", "Nice"),
        ("Lisbon", "Oslo"), ("Valencia", "Seville"), ("Lisbon", "Lyon"), ("Paris", "Tallinn"),
        ("Prague", "Tallinn")
    ]
    
    s = Solver()
    
    # Variables for start days of flexible cities
    city_vars = {}
    for city in cities:
        if cities[city][1] is None:
            start = Int(f"{city}_start")
            duration = cities[city][0]
            end = Int(f"{city}_end")
            s.add(start >= 1, end == start + duration - 1, end <= 25)
            city_vars[city] = (start, end)
        else:
            # Fixed start and end
            city_vars[city] = (cities[city][1], cities[city][2])
    
    # All cities' intervals must be disjoint and cover all days 1-25
    intervals = []
    for city in cities:
        if cities[city][1] is None:
            start, end = city_vars[city]
        else:
            start, end = cities[city][1], cities[city][2]
        intervals.append((start, end))
    
    # Ensure no overlapping intervals and cover all days
    days = [False]*25  # days[0] represents day 1, ..., days[24] is day 25
    for (s, e) in intervals:
        for i in range(25):
            day = i + 1
            s.add(Implies(And(s <= day, day <= e), days[i] == True))
    s.add([d == True for d in days])  # All days must be covered
    
    # Ensure intervals are non-overlapping
    for i in range(len(intervals)):
        s_i_start = intervals[i][0]
        s_i_end = intervals[i][1]
        for j in range(i+1, len(intervals)):
            s_j_start = intervals[j][0]
            s_j_end = intervals[j][1]
            # Intervals i and j do not overlap
            s.add(Or(s_i_end < s_j_start, s_j_end < s_i_start))
    
    # Collect city order based on start times
    city_order = []
    for city in cities:
        if cities[city][1] is None:
            start_var = city_vars[city][0]
        else:
            start_var = cities[city][1]
        city_order.append((start_var, city))
    
    # Sort cities by start day (using a list comprehension to handle variables)
    # This is challenging in Z3; instead, we'll enforce pairwise ordering
    for i in range(len(city_order)):
        for j in range(i+1, len(city_order)):
            # If city i's start < city j's start, then city i must end before city j starts
            s_i_start = city_order[i][0]
            s_i_end = intervals[i][1]
            s_j_start = city_order[j][0]
            s.add(If(s_i_start < s_j_start, s_i_end < s_j_start, True))
            s.add(If(s_j_start < s_i_start, intervals[j][1] < s_i_start, True))
    
    # Ensure consecutive cities in the order have direct flights
    # Extract the city sequence based on sorted start days
    # This is complex in Z3; instead, we'll compare every consecutive pair
    for i in range(len(intervals)):
        for j in range(len(intervals)):
            if i == j:
                continue
            # Check if interval i is immediately before interval j
            i_end = intervals[i][1]
            j_start = intervals[j][0]
            # If j starts right after i ends, they must be connected
            s.add(Implies(j_start == i_end + 1, 
                         Or( (city_order[i][1], city_order[j][1]) in connections,
                             (city_order[j][1], city_order[i][1]) in connections )))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for city in cities:
            if cities[city][1] is None:
                start = m[city_vars[city][0]].as_long()
                end = m[city_vars[city][1]].as_long()
            else:
                start, end = cities[city][1], cities[city][2]
            schedule.append( (start, end, city) )
        schedule.sort()
        print("Trip Plan:")
        for start, end, city in schedule:
            print(f"{city}: Days {start}-{end}")
    else:
        print("No valid trip plan found")

if __name__ == "__main__":
    main()