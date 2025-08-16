from z3 import *
import json

# Return the duration (number of days) for a city given its index.
# City indices are defined as:
# 0: Rome (3 days)
# 1: Mykonos (2 days; must cover day 10 or 11)
# 2: Lisbon (2 days)
# 3: Frankfurt (5 days; wedding between day 1 and 5 must be attended)
# 4: Nice (3 days)
# 5: Stuttgart (4 days)
# 6: Venice (4 days)
# 7: Dublin (2 days)
# 8: Bucharest (2 days)
# 9: Seville (5 days; conference on day 13 and 17 → start exactly day 13)
def get_duration(city):
    return If(city == 0, 3,
           If(city == 1, 2,
           If(city == 2, 2,
           If(city == 3, 5,
           If(city == 4, 3,
           If(city == 5, 4,
           If(city == 6, 4,
           If(city == 7, 2,
           If(city == 8, 2,
           If(city == 9, 5, -1)))))))))))

# Define the direct flight relation. Since flights are bidirectional,
# we list each allowed edge (in both orders) from the given list:
def allowed_edge(a, b):
    return Or(
        And(a == 0, b == 5), And(a == 5, b == 0),        # Rome <-> Stuttgart
        And(a == 0, b == 6), And(a == 6, b == 0),        # Venice <-> Rome
        And(a == 7, b == 8), And(a == 8, b == 7),        # Dublin <-> Bucharest
        And(a == 1, b == 0), And(a == 0, b == 1),        # Mykonos <-> Rome
        And(a == 9, b == 2), And(a == 2, b == 9),        # Seville <-> Lisbon
        And(a == 3, b == 6), And(a == 6, b == 3),        # Frankfurt <-> Venice
        And(a == 6, b == 5), And(a == 5, b == 6),        # Venice <-> Stuttgart
        And(a == 8, b == 2), And(a == 2, b == 8),        # Bucharest <-> Lisbon
        And(a == 4, b == 1), And(a == 1, b == 4),        # Nice <-> Mykonos
        And(a == 6, b == 2), And(a == 2, b == 6),        # Venice <-> Lisbon
        And(a == 7, b == 2), And(a == 2, b == 7),        # Dublin <-> Lisbon
        And(a == 6, b == 4), And(a == 4, b == 6),        # Venice <-> Nice
        And(a == 0, b == 9), And(a == 9, b == 0),        # Rome <-> Seville
        And(a == 3, b == 0), And(a == 0, b == 3),        # Frankfurt <-> Rome
        And(a == 4, b == 7), And(a == 7, b == 4),        # Nice <-> Dublin
        And(a == 0, b == 8), And(a == 8, b == 0),        # Rome <-> Bucharest
        And(a == 3, b == 7), And(a == 7, b == 3),        # Frankfurt <-> Dublin
        And(a == 0, b == 7), And(a == 7, b == 0),        # Rome <-> Dublin
        And(a == 0, b == 2), And(a == 2, b == 0),        # Rome <-> Lisbon
        And(a == 3, b == 2), And(a == 2, b == 3),        # Frankfurt <-> Lisbon
        And(a == 4, b == 0), And(a == 0, b == 4),        # Nice <-> Rome
        And(a == 3, b == 4), And(a == 4, b == 3),        # Frankfurt <-> Nice
        And(a == 3, b == 5), And(a == 5, b == 3),        # Frankfurt <-> Stuttgart
        And(a == 3, b == 8), And(a == 8, b == 3),        # Frankfurt <-> Bucharest
        And(a == 2, b == 5), And(a == 5, b == 2),        # Lisbon <-> Stuttgart
        And(a == 4, b == 2), And(a == 2, b == 4),        # Nice <-> Lisbon
        And(a == 7, b == 9), And(a == 9, b == 7)         # Seville <-> Dublin
    )

def main():
    # List of city names (per the index mapping above)
    cities = ["Rome", "Mykonos", "Lisbon", "Frankfurt", "Nice", 
              "Stuttgart", "Venice", "Dublin", "Bucharest", "Seville"]
    # Their durations, by index (must add up with overlaps to 23 days)
    durations = [3, 2, 2, 5, 3, 4, 4, 2, 2, 5]
    num_cities = 10

    solver = Solver()

    # order_vars[i] will be the city index in the i-th segment
    order_vars = [Int(f"order_{i}") for i in range(num_cities)]
    # s_vars[i] will be the start day of the segment for the city at order_vars[i]
    s_vars = [Int(f"s_{i}") for i in range(num_cities)]

    # Constrain each order variable to be in the range 0..9 (i.e. one of the ten cities)
    for i in range(num_cities):
        solver.add(And(order_vars[i] >= 0, order_vars[i] < num_cities))
    # All cities must be different (each is visited exactly once)
    solver.add(Distinct(order_vars))

    # The first segment must start on Day 1.
    solver.add(s_vars[0] == 1)
    # For each subsequent segment, the start day equals the previous segment’s start day
    # plus that city’s duration minus 1, so that the flight day (the boundary day) counts for both.
    for i in range(num_cities - 1):
        solver.add(s_vars[i+1] == s_vars[i] + get_duration(order_vars[i]) - 1)
    
    # The final city’s end day must be Day 23.
    solver.add(s_vars[num_cities - 1] + get_duration(order_vars[num_cities - 1]) - 1 == 23)

    # Add direct flight connections between consecutive cities.
    for i in range(num_cities - 1):
        solver.add(allowed_edge(order_vars[i], order_vars[i+1]))

    # Add additional time–constraints:
    for i in range(num_cities):
        # If the city in position i is Mykonos (index 1), then its 2–day stay must cover day 10 or 11.
        # (Since a 2–day block starting on day 9 covers days 9–10, on day 10 covers 10–11, and on day 11 covers 11–12.)
        solver.add(Implies(order_vars[i] == 1, Or(s_vars[i] == 9, s_vars[i] == 10, s_vars[i] == 11)))
        # If the city is Frankfurt (index 3), then its block must include a day between 1 and 5.
        # With a 5–day stay, it suffices to require its start day is ≤ 5.
        solver.add(Implies(order_vars[i] == 3, s_vars[i] <= 5))
        # If the city is Seville (index 9), then it must start exactly on day 13
        # so that its 5–day stay covers days 13 through 17 (meeting the conference)
        solver.add(Implies(order_vars[i] == 9, s_vars[i] == 13))
    
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        # For each segment, we compute its start_day and end_day.
        for i in range(num_cities):
            city_idx = m.evaluate(order_vars[i]).as_long()
            start_day = m.evaluate(s_vars[i]).as_long()
            dur = durations[city_idx]  # Use our fixed durations list
            end_day = start_day + dur - 1
            itinerary.append({
                "city": cities[city_idx],
                "start_day": start_day,
                "end_day": end_day
            })
        # Create the final JSON object.
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()