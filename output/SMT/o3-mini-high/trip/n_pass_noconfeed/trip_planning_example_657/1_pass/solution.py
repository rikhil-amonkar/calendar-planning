import json
from z3 import *

def main():
    solver = Solver()
    num_segments = 6

    # Define variables for each segment:
    # city_vars[i] is an Int representing the city for segment i
    # s[i] is the start day for segment i.
    city_vars = [Int(f"city_{i}") for i in range(num_segments)]
    s = [Int(f"s_{i}") for i in range(num_segments)]

    # Mapping of city indices to names:
    # 0: Frankfurt, 1: Manchester, 2: Valencia, 3: Naples, 4: Oslo, 5: Vilnius
    cities = ["Frankfurt", "Manchester", "Valencia", "Naples", "Oslo", "Vilnius"]
    # Required stay durations for each city:
    durations = [4, 4, 4, 4, 3, 2]

    # Each city variable must be between 0 and 5 and all must be distinct
    for cv in city_vars:
        solver.add(And(cv >= 0, cv < 6))
    solver.add(Distinct(city_vars))
    
    # The itinerary starts at day 1.
    solver.add(s[0] == 1)

    # Define a helper expression to get the duration associated with a city variable.
    def get_duration(city_expr):
        return If(city_expr == 0, 4,
               If(city_expr == 1, 4,
               If(city_expr == 2, 4,
               If(city_expr == 3, 4,
               If(city_expr == 4, 3, 2)))))

    # Consecutive segments: if flying on day X, then you are in both cities on day X.
    # Thus the start day of segment (i+1) is: s[i+1] = s[i] + (duration of segment i) - 1.
    for i in range(num_segments - 1):
        solver.add(s[i+1] == s[i] + get_duration(city_vars[i]) - 1)

    # The overall trip must finish on day 16.
    solver.add(s[num_segments - 1] + get_duration(city_vars[num_segments - 1]) - 1 == 16)

    # We want to attend an annual show in Frankfurt from day 13 to day 16.
    # To fully cover days 13-16 with a 4-day stay, we force Frankfurt (0) to be the final city.
    solver.add(city_vars[num_segments - 1] == 0)
    solver.add(s[num_segments - 1] == 13)  # Frankfurt's stay will then span days 13-16.

    # Allowed direct flights (bidirectional) between cities (using city indices):
    # - Valencia and Frankfurt: (2,0)
    # - Manchester and Frankfurt: (1,0)
    # - Naples and Manchester: (3,1)
    # - Naples and Frankfurt: (3,0)
    # - Naples and Oslo: (3,4)
    # - Oslo and Frankfurt: (4,0)
    # - Vilnius and Frankfurt: (5,0)
    # - Oslo and Vilnius: (4,5)
    # - Manchester and Oslo: (1,4)
    # - Valencia and Naples: (2,3)
    allowed_flights = [(0,2), (0,1), (1,3), (0,3), (3,4), (0,4), (0,5), (4,5), (1,4), (2,3)]
    
    # For each consecutive pair, enforce that the flight between the two cities is direct.
    for i in range(num_segments - 1):
        conditions = []
        for (a, b) in allowed_flights:
            conditions.append(And(city_vars[i] == a, city_vars[i+1] == b))
            conditions.append(And(city_vars[i] == b, city_vars[i+1] == a))
        solver.add(Or(conditions))
    
    # There is a wedding in Vilnius between day 12 and day 13.
    # If Vilnius (5) is visited on segment i, then its start day s[i] must allow being
    # there on either day 12 or day 13. Since Vilnius is a 2-day visit, requiring s[i] to be in [11, 13]
    # guarantees that at least one of day 12 or day 13 is included.
    for i in range(num_segments):
        solver.add(Implies(city_vars[i] == 5, And(s[i] >= 11, s[i] <= 13)))
    
    # Solve the SMT model.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_segments):
            start_day = model.evaluate(s[i]).as_long()
            city_index = model.evaluate(city_vars[i]).as_long()
            duration_val = durations[city_index]
            end_day = start_day + duration_val - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()