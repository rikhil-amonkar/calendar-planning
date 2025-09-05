from z3 import *
import json

# Mapping cities to integers
ISTANBUL, LONDON, SANTORINI = 0, 1, 2
city_names = {ISTANBUL: "Istanbul", LONDON: "London", SANTORINI: "Santorini"}

# Total number of travel days
TOTAL_DAYS = 10

# Create solver instance
s = Solver()

# Create flight day markers as integer variables
# f1 and f2 represent the two flight days (1-indexed)
f1 = Int('f1')
f2 = Int('f2')
s.add(f1 >= 1, f1 <= TOTAL_DAYS, f2 >= 1, f2 <= TOTAL_DAYS, f1 < f2)

# Create lists for start and end city for each day (1-indexed: day i corresponds to index i-1)
start = [Int(f"start_{d}") for d in range(1, TOTAL_DAYS + 1)]
end = [Int(f"end_{d}") for d in range(1, TOTAL_DAYS + 1)]

# Add domain constraints for each day's cities
for d in range(TOTAL_DAYS):
    s.add(Or(start[d] == ISTANBUL, start[d] == LONDON, start[d] == SANTORINI))
    s.add(Or(end[d] == ISTANBUL, end[d] == LONDON, end[d] == SANTORINI))

# The traveler starts in Istanbul on day 1
s.add(start[0] == ISTANBUL)

# For each day, determine if it's a flight day.
# If day d is a flight day (i.e. d equals f1 or f2), then the traveler takes a flight:
#   - They are in two cities that day: the origin (start) and destination (end).
#   - The flight day must have a change of city (start != end).
#   - We constrain the flight routes: first flight (day f1) must be Istanbul -> London,
#     and second flight (day f2) must be London -> Santorini.
# Otherwise, if not a flight day, then they stay in the same city: start == end.
for d in range(1, TOTAL_DAYS + 1):
    sd = start[d - 1]
    ed = end[d - 1]
    # isFlight is true if the current day equals f1 or f2.
    isFlight = Or(f1 == d, f2 == d)
    # For flight day, ensure a change of city and the proper flight connection.
    flight_constraints = And(
        sd != ed,
        And(Implies(f1 == d, And(sd == ISTANBUL, ed == LONDON)),
            Implies(f2 == d, And(sd == LONDON, ed == SANTORINI)))
    )
    s.add(If(isFlight, flight_constraints, sd == ed))

# Ensure continuity: for each day after day 1, the start of a day equals the previous day's end.
for d in range(2, TOTAL_DAYS + 1):
    s.add(start[d - 1] == end[d - 2])

# Conference constraints: on day 5 and day 10, the traveler must attend a conference in Santorini.
# If a conference day is a flight day, then either the start or the end of that day must be Santorini.
day5_isFlight = Or(f1 == 5, f2 == 5)
s.add(If(day5_isFlight, Or(start[4] == SANTORINI, end[4] == SANTORINI), start[4] == SANTORINI))

day10_isFlight = Or(f1 == 10, f2 == 10)
s.add(If(day10_isFlight, Or(start[9] == SANTORINI, end[9] == SANTORINI), start[9] == SANTORINI))

# Calculate total days contributed to each city.
# On a non-flight day, the contribution is 1 for the city in start[d].
# On a flight day, the contribution is 1 for start[d] and 1 for end[d].
def city_contribution(day_index, city):
    # day_index is 0-indexed; actual day is day_index+1
    day_num = day_index + 1
    isFlight = Or(f1 == day_num, f2 == day_num)
    return If(isFlight, If(start[day_index] == city, 1, 0) + If(end[day_index] == city, 1, 0),
              If(start[day_index] == city, 1, 0))

total_istanbul = Sum([city_contribution(d, ISTANBUL) for d in range(TOTAL_DAYS)])
total_london = Sum([city_contribution(d, LONDON) for d in range(TOTAL_DAYS)])
total_santorini = Sum([city_contribution(d, SANTORINI) for d in range(TOTAL_DAYS)])

# Add constraints for required duration in each city.
s.add(total_istanbul == 3)
s.add(total_london == 3)
s.add(total_santorini == 6)

# Check for a solution
if s.check() == sat:
    m = s.model()
    # Extract flight day values and convert them to int
    f1_val = m[f1].as_long()
    f2_val = m[f2].as_long()
    
    # Get the starting city of day 1
    seg1_city = m[start[0]].as_long()
    # For the first flight day, the arrival city is end[f1-1] (since days are 1-indexed)
    seg2_city = m[end[f1_val - 1]].as_long()
    # For the second flight day, the arrival city is end[f2-1]
    seg3_city = m[end[f2_val - 1]].as_long()
    
    # Construct itinerary segments.
    itinerary = [
        {"day_range": f"Day 1-{f1_val}", "place": city_names[seg1_city]},
        {"day_range": f"Day {f1_val}-{f2_val}", "place": city_names[seg2_city]},
        {"day_range": f"Day {f2_val}-10", "place": city_names[seg3_city]}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"error": "No valid itinerary found"}))