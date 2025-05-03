from z3 import *

# City indices and durations:
# 0: Porto     (3 days)
# 1: Helsinki  (5 days)
# 2: Lyon      (2 days)  - Wedding in Lyon between day 3 and 4 → force arrival = 3.
# 3: Rome      (5 days)  - Workshop in Rome between day 4 and 8 → force arrival = 4.
# 4: Krakow    (2 days)
# 5: Dublin    (5 days)  - Conference in Dublin between day 12 and 16 → force arrival = 12.
# 6: London    (2 days)
#
# Sum of raw durations = 3 + 5 + 2 + 5 + 2 + 5 + 2 = 24 days.
# There are 6 overlapping transit days between the 7 visits,
# so the overall trip length is 24 - 6 = 18 days.

cities = ["Porto", "Helsinki", "Lyon", "Rome", "Krakow", "Dublin", "London"]
durations = [3, 5, 2, 5, 2, 5, 2]

# Allowed direct flights (bidirectional):
# 1. Rome and Helsinki         => (Rome, Helsinki): (3,1)
# 2. Lyon and Rome             => (Lyon, Rome): (2,3)
# 3. Krakow and Helsinki       => (Krakow, Helsinki): (4,1)
# 4. Lyon and Dublin           => (Lyon, Dublin): (2,5)
# 5. Krakow and London         => (Krakow, London): (4,6)
# 6. London and Lyon           => (London, Lyon): (6,2)
# 7. Helsinki and Dublin       => (Helsinki, Dublin): (1,5)
# 8. London and Dublin         => (London, Dublin): (6,5)
# 9. Krakow and Dublin         => (Krakow, Dublin): (4,5)
# 10. Lyon and Porto           => (Lyon, Porto): (2,0)
# 11. London and Helsinki      => (London, Helsinki): (6,1)
# 12. Rome and Dublin          => (Rome, Dublin): (3,5)
# 13. Dublin and Porto         => (Dublin, Porto): (5,0)
# 14. London and Rome          => (London, Rome): (6,3)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

add_bidirectional(3, 1)  # Rome <-> Helsinki
add_bidirectional(2, 3)  # Lyon <-> Rome
add_bidirectional(4, 1)  # Krakow <-> Helsinki
add_bidirectional(2, 5)  # Lyon <-> Dublin
add_bidirectional(4, 6)  # Krakow <-> London
add_bidirectional(6, 2)  # London <-> Lyon
add_bidirectional(1, 5)  # Helsinki <-> Dublin
add_bidirectional(6, 5)  # London <-> Dublin
add_bidirectional(4, 5)  # Krakow <-> Dublin
add_bidirectional(2, 0)  # Lyon <-> Porto
add_bidirectional(6, 1)  # London <-> Helsinki
add_bidirectional(3, 5)  # Rome <-> Dublin
add_bidirectional(5, 0)  # Dublin <-> Porto
add_bidirectional(6, 3)  # London <-> Rome

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Modeling the order of visits as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure days for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]
# The trip starts on day 1.
s.add(arrivals[0] == 1)

# Compute departure day for each visit: departure = arrival + duration - 1.
for i in range(n):
    constraints = []
    for c in range(n):
        constraints.append(If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False))
    s.add(Or(constraints))

# Consecutive visits: next arrival equals the previous departure.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 18.
s.add(departures[n-1] == 18)

# Event-specific constraints:
# Lyon (city index 2): Wedding between day 3 and day 4 → force arrival = 3.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 3, True))
# Rome (city index 3): Workshop between day 4 and day 8 → force arrival = 4.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 4, True))
# Dublin (city index 5): Conference between day 12 and day 16 → force arrival = 12.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 12, True))

# Connectivity constraints:
# Each consecutive pair must be connected by an allowed direct flight.
for i in range(n - 1):
    conn_options = []
    for (frm, to) in allowed_flights:
        conn_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(conn_options))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:9s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")