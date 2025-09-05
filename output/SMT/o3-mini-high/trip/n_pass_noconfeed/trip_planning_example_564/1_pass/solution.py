from z3 import *
import json

# Define cities and their fixed durations
# City indices:
# 0: Istanbul, 1: Rome, 2: Seville, 3: Naples, 4: Santorini
city_names = ["Istanbul", "Rome", "Seville", "Naples", "Santorini"]
durations = [2, 3, 4, 7, 4]  # corresponding days spent in each city

# Allowed direct flight pairs (bidirectional)
# Each tuple (a, b) means a direct flight is allowed between city a and city b.
allowed_flights = [
    (0, 1), (1, 0),  # Rome <--> Istanbul
    (1, 4), (4, 1),  # Rome <--> Santorini
    (2, 1), (1, 2),  # Seville <--> Rome
    (0, 3), (3, 0),  # Istanbul <--> Naples
    (1, 3), (3, 1),  # Rome <--> Naples
    (3, 4), (4, 3)   # Naples <--> Santorini
]

# Total trip days
total_days = 16

# Number of cities in the itinerary
n = 5

# Create a Z3 solver instance
s = Solver()

# Create decision variables for the order (itinerary positions)
order_vars = [Int(f"order_{i}") for i in range(n)]
for ov in order_vars:
    s.add(And(ov >= 0, ov < n))
# Add permutation constraint: all order_vars must be distinct
for i in range(n):
    for j in range(i+1, n):
        s.add(order_vars[i] != order_vars[j])

# Create decision variables for start days of each city segment in the itinerary
start_vars = [Int(f"S_{i}") for i in range(n)]
for sv in start_vars:
    s.add(sv >= 1)  # each segment starts on at least day 1

# Helper: Given an order variable (which is an Int representing a city), return its duration as a Z3 expression.
def city_duration(city_var):
    return If(city_var == 0, durations[0],
           If(city_var == 1, durations[1],
           If(city_var == 2, durations[2],
           If(city_var == 3, durations[3],
           If(city_var == 4, durations[4], 0)))))

# Chain constraints: The itinerary is a continuous sequence.
# The first city must start on day 1.
s.add(start_vars[0] == 1)
# For subsequent positions, the start day is the previous start plus the previous city's full days,
# minus 1 because the flight day is counted in both cities.
for i in range(n - 1):
    # S[i+1] = S[i] + duration(city at order[i]) - 1
    s.add(start_vars[i+1] == start_vars[i] + city_duration(order_vars[i]) - 1)

# The trip finishes exactly on total_days. For the last city, its interval is [S, S + d - 1] = total days.
s.add(start_vars[n-1] + city_duration(order_vars[n-1]) - 1 == total_days)

# Allowed flight constraints: for each consecutive pair in the itinerary, ensure there is a direct flight.
for i in range(1, n):
    # Build condition that (order_vars[i-1], order_vars[i]) is one of the allowed flight pairs.
    flight_possible = []
    for (a, b) in allowed_flights:
        flight_possible.append(And(order_vars[i-1] == a, order_vars[i] == b))
    s.add(Or(flight_possible))

# Special constraint for Istanbul:
# You want to spend 2 days in Istanbul and visit relatives in Istanbul between day 6 and day 7.
# Istanbul's duration is 2. To cover days 6 and 7, its start day must be exactly 6.
for i in range(n):
    s.add(Implies(order_vars[i] == 0, start_vars[i] == 6))

# Special constraint for Santorini:
# You want to spend 4 days in Santorini and attend a wedding in Santorini between day 13 and day 16.
# Santorini's 4-day interval is [S, S+3]. To cover at least one day between 13 and 16, we require S+3 >= 13.
# Equivalently, S >= 10. Also, the start should not be later than day 16.
for i in range(n):
    s.add(Implies(order_vars[i] == 4, And(start_vars[i] >= 10, start_vars[i] <= total_days)))

# (Rome, Seville, Naples) have their durations already set and the remaining constraints will decide the order.
# The overall chained time constraint forces an overlap of flight days:
# Sum(durations) - (n - 1) == total_days   i.e.,  (2+3+4+7+4) - 4 == 16

# Check satisfiability and extract the model if one exists
if s.check() == sat:
    m = s.model()
    itinerary = []
    # For each position in the itinerary, compute the day range and city name.
    for i in range(n):
        # Evaluate the city in the itinerary for this position
        city_idx = m.evaluate(order_vars[i]).as_long()
        start_day = m.evaluate(start_vars[i]).as_long()
        duration_val = durations[city_idx]
        end_day = start_day + duration_val - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_names[city_idx]
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))