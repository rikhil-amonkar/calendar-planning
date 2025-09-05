#!/usr/bin/env python3
from z3 import *
import json

# Map city indices to names and durations.
# City indices:
# 0: Warsaw (3 days)
# 1: Porto (5 days)
# 2: Naples (4 days)
# 3: Brussels (3 days)
# 4: Split (3 days)
# 5: Reykjavik (5 days)
# 6: Amsterdam (4 days)
# 7: Lyon (3 days)
# 8: Helsinki (4 days)
# 9: Valencia (2 days)
city_names = {
    0: "Warsaw",
    1: "Porto",
    2: "Naples",
    3: "Brussels",
    4: "Split",
    5: "Reykjavik",
    6: "Amsterdam",
    7: "Lyon",
    8: "Helsinki",
    9: "Valencia"
}

durations = {
    0: 3,
    1: 5,
    2: 4,
    3: 3,
    4: 3,
    5: 5,
    6: 4,
    7: 3,
    8: 4,
    9: 2
}

# Define a helper function to build a Z3 expression for a city's duration
def duration_expr(city):
    return If(city == 0, 3,
           If(city == 1, 5,
           If(city == 2, 4,
           If(city == 3, 3,
           If(city == 4, 3,
           If(city == 5, 5,
           If(city == 6, 4,
           If(city == 7, 3,
           If(city == 8, 4,
           If(city == 9, 2, 0))))))))))

# List of allowed direct flights (considered bidirectional)
allowed_flights = [
    (6, 0), (0, 6),                    # Amsterdam - Warsaw
    (8, 3), (3, 8),                    # Helsinki - Brussels
    (8, 0), (0, 8),                    # Helsinki - Warsaw
    (5, 3), (3, 5),                    # Reykjavik - Brussels
    (6, 7), (7, 6),                    # Amsterdam - Lyon
    (6, 2), (2, 6),                    # Amsterdam - Naples
    (6, 5), (5, 6),                    # Amsterdam - Reykjavik
    (2, 9), (9, 2),                    # Naples - Valencia
    (1, 3), (3, 1),                    # Porto - Brussels
    (6, 4), (4, 6),                    # Amsterdam - Split
    (7, 4), (4, 7),                    # Lyon - Split
    (0, 4), (4, 0),                    # Warsaw - Split
    (1, 6), (6, 1),                    # Porto - Amsterdam
    (8, 4), (4, 8),                    # Helsinki - Split
    (3, 7), (7, 3),                    # Brussels - Lyon
    (1, 7), (7, 1),                    # Porto - Lyon
    (5, 0), (0, 5),                    # Reykjavik - Warsaw
    (3, 9), (9, 3),                    # Brussels - Valencia
    (9, 7), (7, 9),                    # Valencia - Lyon
    (1, 0), (0, 1),                    # Porto - Warsaw
    (0, 9), (9, 0),                    # Warsaw - Valencia
    (6, 8), (8, 6),                    # Amsterdam - Helsinki
    (1, 9), (9, 1),                    # Porto - Valencia
    (0, 3), (3, 0),                    # Warsaw - Brussels
    (0, 2), (2, 0),                    # Warsaw - Naples
    (2, 4), (4, 2),                    # Naples - Split
    (8, 2), (2, 8),                    # Helsinki - Naples
    (8, 5), (5, 8),                    # Helsinki - Reykjavik
    (6, 9), (9, 6),                    # Amsterdam - Valencia
    (2, 3), (3, 2)                     # Naples - Brussels
]

def main():
    s = Solver()

    num_cities = 10  # There are 10 segments in the itinerary.
    
    # Create integer variables for the order (city indices) and start days.
    cities = [Int(f"city_{i}") for i in range(num_cities)]
    start_days = [Int(f"s_{i}") for i in range(num_cities)]
    
    # Each city variable must be between 0 and 9.
    for i in range(num_cities):
        s.add(And(cities[i] >= 0, cities[i] <= 9))
    # Enforce that each city appears exactly once.
    s.add(Distinct(cities))
    
    # The itinerary is defined by segments that overlap on flight days.
    # s_0 is Day 1.
    s.add(start_days[0] == 1)
    # For each subsequent segment, the start day is the finish of the previous segment.
    for i in range(1, num_cities):
        s.add(start_days[i] == start_days[i-1] + duration_expr(cities[i-1]) - 1)
    # The overall trip must finish on Day 27.
    s.add(start_days[num_cities - 1] + duration_expr(cities[num_cities - 1]) - 1 == 27)
    
    # Flight connectivity: for each consecutive pair, there must be a direct flight.
    for i in range(num_cities - 1):
        possible = []
        for (a, b) in allowed_flights:
            possible.append(And(cities[i] == a, cities[i+1] == b))
        s.add(Or(possible))
    
    # Event constraints:
    for i in range(num_cities):
        # Workshop in Porto (city 1) between Day 1 and 5:
        s.add(Implies(cities[i] == 1, start_days[i] <= 5))
        
        # Conference in Naples (city 2) on days 17 and 20:
        # Since Naples is visited for 4 days, the only way to include both days 17 and 20 is to have s = 17.
        s.add(Implies(cities[i] == 2, start_days[i] == 17))
        
        # Annual show in Brussels (city 3) from Day 20 to 22:
        # Brussels is 3 days so it must start on Day 20.
        s.add(Implies(cities[i] == 3, start_days[i] == 20))
        
        # Visit relatives in Amsterdam (city 6) between Day 5 and 8.
        # Amsterdam is 4 days so its interval [s, s+3] must intersect [5,8]:
        s.add(Implies(cities[i] == 6, And(start_days[i] <= 8, start_days[i] + 3 >= 5)))
        
        # Attend wedding in Helsinki (city 8) between Day 8 and 11.
        # Helsinki is 4 days so its interval [s, s+3] must intersect [8,11]:
        s.add(Implies(cities[i] == 8, And(start_days[i] <= 11, start_days[i] + 3 >= 8)))
    
    # Solve for a valid itinerary.
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for i in range(num_cities):
            city_idx = m.evaluate(cities[i]).as_long()
            city_name = city_names[city_idx]
            start_day = m.evaluate(start_days[i]).as_long()
            finish_day = start_day + durations[city_idx] - 1
            itinerary_list.append({"day_range": f"Day {start_day}-{finish_day}", "place": city_name})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        # If no itinerary is found, return an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()