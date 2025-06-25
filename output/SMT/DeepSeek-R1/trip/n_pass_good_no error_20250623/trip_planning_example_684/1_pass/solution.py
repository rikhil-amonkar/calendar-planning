from z3 import *

def main():
    # City indices: 0=Amsterdam, 1=Edinburgh, 2=Brussels, 3=Vienna, 4=Berlin, 5=Reykjavik
    city_names = ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik']
    reqs = [4, 5, 5, 5, 4, 5]  # required days for each city

    # Flight edges as sorted tuples (min, max)
    flight_edges = [
        (0, 1), (0, 3), (0, 4), (0, 5),
        (1, 2), (1, 4),
        (2, 3), (2, 4), (2, 5),
        (3, 4), (3, 5),
        (4, 5)
    ]

    # Create Z3 variables
    n_segments = 6
    city = [Int(f'city_{i}') for i in range(n_segments)]
    start = [Int(f'start_{i}') for i in range(n_segments)]
    end = [Int(f'end_{i}') for i in range(n_segments)]

    s = Solver()

    # Each city variable is between 0 and 5
    for i in range(n_segments):
        s.add(city[i] >= 0, city[i] < 6)

    # All cities are distinct
    s.add(Distinct(city))

    # Timeline constraints: starts at day 1, ends at day 23, contiguous segments
    s.add(start[0] == 1)
    s.add(end[5] == 23)
    for i in range(n_segments - 1):
        s.add(start[i+1] == end[i])

    # Stay duration constraints
    for i in range(n_segments):
        dur = end[i] - start[i] + 1
        s.add(If(city[i] == 0, dur == 4,
                If(city[i] == 1, dur == 5,
                If(city[i] == 2, dur == 5,
                If(city[i] == 3, dur == 5,
                If(city[i] == 4, dur == 4, dur == 5))))))

    # Flight connectivity constraints
    for i in range(n_segments - 1):
        u = city[i]
        v = city[i+1]
        low = If(u < v, u, v)
        high = If(u < v, v, u)
        conds = []
        for edge in flight_edges:
            conds.append(And(low == edge[0], high == edge[1]))
        s.add(Or(conds))

    # Special constraints for Amsterdam, Berlin, Reykjavik
    ams_constraint = Or([And(city[i] == 0, start[i] <= 8, end[i] >= 5) for i in range(n_segments)])
    s.add(ams_constraint)

    berlin_constraint = Or([And(city[i] == 4, start[i] <= 19, end[i] >= 16) for i in range(n_segments)])
    s.add(berlin_constraint)

    reyk_constraint = Or([And(city[i] == 5, start[i] <= 16, end[i] >= 12) for i in range(n_segments)])
    s.add(reyk_constraint)

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        # Build the itinerary
        itinerary = []
        for i in range(n_segments):
            c_idx = m.eval(city[i]).as_long()
            c_name = city_names[c_idx]
            s_val = m.eval(start[i]).as_long()
            e_val = m.eval(end[i]).as_long()
            itinerary.append({'day_range': f"Day {s_val}-{e_val}", 'place': c_name})
            if i < n_segments - 1:
                next_c_idx = m.eval(city[i+1]).as_long()
                next_c_name = city_names[next_c_idx]
                itinerary.append({'day_range': f"Day {e_val}", 'place': c_name})
                itinerary.append({'day_range': f"Day {e_val}", 'place': next_c_name})
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()