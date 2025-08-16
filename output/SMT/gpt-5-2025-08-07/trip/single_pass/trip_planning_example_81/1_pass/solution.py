from z3 import *
import json

# Cities
MYKONOS, BUDAPEST, HAMBURG = 0, 1, 2
city_names = {MYKONOS: "Mykonos", BUDAPEST: "Budapest", HAMBURG: "Hamburg"}

# Problem parameters
num_days = 9

# Decision variables: city[d] is the city assigned for day d (1-based indexing for readability)
city = [Int(f"city_{d}") for d in range(1, num_days + 1)]

s = Solver()

# Domain constraints
for d in range(num_days):
    s.add(Or(city[d] == MYKONOS, city[d] == BUDAPEST, city[d] == HAMBURG))

# Must be in Mykonos on day 4 and day 9 (conference days)
s.add(city[3] == MYKONOS)  # day 4
s.add(city[8] == MYKONOS)  # day 9

# Count flights (transitions between consecutive days)
flights = []
for d in range(1, num_days):  # transitions from day d to day d+1 (0-based indexing)
    flights.append(If(city[d] != city[d-1], 1, 0))

# Exactly 2 flights (because total desired day-count sum is 11 and 9 + flights = 11)
s.add(Sum(flights) == 2)

# Allowed direct flights only when a transition occurs
def allowed_transition(prev, curr):
    return Or(
        And(prev == MYKONOS, curr == BUDAPEST),
        And(prev == BUDAPEST, curr == MYKONOS),
        And(prev == HAMBURG,  curr == BUDAPEST),
        And(prev == BUDAPEST, curr == HAMBURG),
    )

for d in range(1, num_days):
    s.add(Implies(city[d] != city[d-1], allowed_transition(city[d-1], city[d])))

# Compute total days per city with flight days counted for both cities
def total_days_for(c):
    # Occurrences where the day is assigned to city c
    occurrences = Sum([If(city[d] == c, 1, 0) for d in range(num_days)])
    # Additional counts for flight days where previous day city is c (since flight day counts for both)
    extra_from_flights = Sum([If(And(city[d-1] == c, city[d] != city[d-1]), 1, 0) for d in range(1, num_days)])
    return occurrences + extra_from_flights

# Desired totals: Mykonos 6, Budapest 3, Hamburg 2
s.add(total_days_for(MYKONOS) == 6)
s.add(total_days_for(BUDAPEST) == 3)
s.add(total_days_for(HAMBURG) == 2)

# Solve
if s.check() == sat:
    m = s.model()
    itinerary = []
    for d in range(num_days):
        city_val = m.evaluate(city[d]).as_long()
        itinerary.append({"day": d + 1, "place": city_names[city_val]})
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))
else:
    print(json.dumps({"itinerary": []}, ensure_ascii=False))