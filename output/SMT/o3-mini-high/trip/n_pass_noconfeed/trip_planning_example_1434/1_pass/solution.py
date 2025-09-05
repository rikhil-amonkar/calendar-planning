from z3 import *
import json

# Define a function to return the duration (in days) corresponding to each city.
# City indices:
# 0: Rome (3 days)
# 1: Mykonos (2 days)
# 2: Lisbon (2 days)
# 3: Frankfurt (5 days)
# 4: Nice (3 days)
# 5: Stuttgart (4 days)
# 6: Venice (4 days)
# 7: Dublin (2 days)
# 8: Bucharest (2 days)
# 9: Seville (5 days)
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
           If(city == 9, 5, 0))))))))))

# Mapping from index to city name and fixed duration
cities_info = {
    0: ("Rome", 3),
    1: ("Mykonos", 2),
    2: ("Lisbon", 2),
    3: ("Frankfurt", 5),
    4: ("Nice", 3),
    5: ("Stuttgart", 4),
    6: ("Venice", 4),
    7: ("Dublin", 2),
    8: ("Bucharest", 2),
    9: ("Seville", 5)
}

# Allowed direct flight connections.
# The flights are undirected, so a flight between A and B is the same as between B and A.
allowed_flights = [
    (0, 5),  # Rome and Stuttgart
    (0, 6),  # Rome and Venice (via Venice and Rome)
    (0, 1),  # Rome and Mykonos (via Mykonos and Rome)
    (2, 9),  # Lisbon and Seville (via Seville and Lisbon)
    (3, 6),  # Frankfurt and Venice
    (5, 6),  # Stuttgart and Venice (via Venice and Stuttgart)
    (2, 8),  # Lisbon and Bucharest (via Bucharest and Lisbon)
    (1, 4),  # Mykonos and Nice (via Nice and Mykonos)
    (2, 6),  # Lisbon and Venice (via Venice and Lisbon)
    (2, 7),  # Lisbon and Dublin (via Dublin and Lisbon)
    (4, 6),  # Nice and Venice (via Venice and Nice)
    (0, 9),  # Rome and Seville
    (0, 3),  # Rome and Frankfurt (via Frankfurt and Rome)
    (4, 7),  # Nice and Dublin (via Dublin and Nice)
    (0, 8),  # Rome and Bucharest
    (3, 7),  # Frankfurt and Dublin
    (0, 7),  # Rome and Dublin
    (6, 7),  # Venice and Dublin
    (0, 2),  # Rome and Lisbon
    (2, 3),  # Lisbon and Frankfurt (via Frankfurt and Lisbon)
    (0, 4),  # Rome and Nice (via Nice and Rome)
    (3, 4),  # Frankfurt and Nice
    (3, 5),  # Frankfurt and Stuttgart
    (3, 8),  # Frankfurt and Bucharest
    (2, 5),  # Lisbon and Stuttgart
    (2, 4),  # Lisbon and Nice (via Nice and Lisbon)
    (7, 9)   # Dublin and Seville (via Seville and Dublin)
]

def main():
    solver = Solver()

    # We plan to visit 10 cities in a fixed order.
    # route[i] is the city (as an integer index) visited on the i-th segment.
    route = [Int(f"city_{i}") for i in range(10)]
    # start[i] is the day when the stay in the route[i] city begins.
    start = [Int(f"s_{i}") for i in range(10)]
    
    # Each city variable must be between 0 and 9.
    for i in range(10):
        solver.add(route[i] >= 0, route[i] <= 9)
        # The start day of each segment must be between Day 1 and Day 23.
        solver.add(start[i] >= 1, start[i] <= 23)
    
    # The cities must be a permutation of the 10 options.
    solver.add(Distinct(route))
    
    # The itinerary must start on Day 1.
    solver.add(start[0] == 1)
    
    # Link the start times. When flying directly, the flight happens on the transition day.
    # If the stay in city i lasts d days, then the next city is reached on day: start[i+1] = start[i] + d - 1.
    for i in range(9):
        d_i = get_duration(route[i])
        solver.add(start[i+1] == start[i] + d_i - 1)

    # Total itinerary duration constraint: the last segment must end on day 23.
    solver.add(start[9] + get_duration(route[9]) - 1 == 23)
    
    # Flight constraints: consecutive cities must be connected by a direct flight.
    for i in range(9):
        allowed = []
        for (a, b) in allowed_flights:
            # Since flights are undirected, check both orders.
            allowed.append(And(route[i] == a, route[i+1] == b))
            allowed.append(And(route[i] == b, route[i+1] == a))
        solver.add(Or(allowed))
    
    # Special event constraints:
    # Mykonos: Visit duration is 2 days and friends must be met on either Day 10 or Day 11.
    # This means that if Mykonos is visited, its stay should include day 10 or day 11.
    for i in range(10):
        solver.add(Implies(route[i] == 1, Or(start[i] == 9, start[i] == 10, start[i] == 11)))
    
    # Frankfurt: Stay 5 days, and the wedding must occur between Day 1 and Day 5.
    # This is achieved by ensuring the start day is at most 5 so that at least one day of the 5-day stay is within 1-5.
    for i in range(10):
        solver.add(Implies(route[i] == 3, start[i] <= 5))
    
    # Seville: Stay 5 days and attend a conference on Day 13 and Day 17;
    # the only way to ensure this is to start in Seville on Day 13 so that the stay covers days 13-17.
    for i in range(10):
        solver.add(Implies(route[i] == 9, start[i] == 13))
    
    # Check for a solution.
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        for i in range(10):
            city_index = m.evaluate(route[i]).as_long()
            city_name, fixed_duration = cities_info[city_index]
            start_day = m.evaluate(start[i]).as_long()
            end_day = start_day + fixed_duration - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_name
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        # If no solution is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()