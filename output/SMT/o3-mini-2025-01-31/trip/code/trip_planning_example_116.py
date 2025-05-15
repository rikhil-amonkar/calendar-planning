from z3 import *

# City indices and requirements:
# 0: Split      – 6 days.
# 1: Santorini  – 7 days; event: attend a conference in Santorini on day 12 and day 18.
# 2: London     – 7 days.
city_names = ["Split", "Santorini", "London"]
req = [6, 7, 7]  # Total required day credits = 6 + 7 + 7 = 20

# Total base days = 18.
# On a day with no flight you get 1 credit for that city.
# On a flight day, if you fly from city A to city B on that day,
# you are counted as being in both A and B, giving 2 credits.
# Total credits = base days + (# flights) = 18 + (# flights).
# We need 20 total credits, so we require exactly 2 flights.
# That divides the trip into 3 segments – one for each visited city.

DAYS = 18
REQUIRED_FLIGHTS = 2  # exactly

# Allowed direct flights:
# The following flights are allowed (each pair is directed):
# London and Santorini: (2,1) and (1,2)
# Split and London: (0,2) and (2,0)
allowed_flights = [
    (2,1), (1,2),   # London <--> Santorini
    (0,2), (2,0)    # Split <--> London
]

# We fix the order of segments to be:
# Segment 1: Split, Segment 2: London, Segment 3: Santorini.
# The flights must therefore be:
# Flight 1: from Split to London.
# Flight 2: from London to Santorini.

# We introduce auxiliary integer variables d1 and d2 to denote the days on which flights occur.
# They are chosen from days 1...DAYS-1 (day indices are 0-based; day 0 is fixed start).
d1 = Int("d1")  # day index of first flight
d2 = Int("d2")  # day index of second flight

s = Solver()

# 1. Domain constraints for d1 and d2.
s.add(d1 >= 1, d1 < d2, d2 < DAYS)

# 2. Create variables for each day:
# c[d]: the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: Boolean variable that is True if a flight occurs on day d.
# We will force flight[d] to be true only for d == d1 or d == d2.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: Boolean variable that is True if day d is the start of a new segment (i.e. has a flight).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

# 3. Domain constraint: each c[d] must be one of the cities 0..2.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 4. Define flight variables based on d1 and d2.
# For day 0, there's no flight.
s.add(flight[0] == False)
# For day d from 1 to DAYS-1, enforce: flight[d] is true if and only if d equals d1 or d equals d2.
for d in range(1, DAYS):
    s.add(flight[d] == Or(d == d1, d == d2))
    
# 5. Define isSeg: day 0 is always a segment start; for d>=1, isSeg[d] if a flight occurs.
s.add(isSeg[0] == True)
for d in range(1, DAYS):
    s.add(isSeg[d] == flight[d])
    
# 6. Enforce the ordering of segments (i.e. which city is visited in each segment):
# We want:
#   - the first segment (starting at day 0) to be Split (city 0),
#   - the segment starting on day d1 (first flight day) to be London (city 2),
#   - the segment starting on day d2 (second flight day) to be Santorini (city 1).
s.add(c[0] == 0)
s.add(Implies(flight[d1], c[d1] == 2))
s.add(Implies(flight[d2], c[d2] == 1))

# 7. Flight transition constraints:
# For every day d from 1 to DAYS-1, if a flight occurs then the move from day d-1 to d
# must be allowed.
for d in range(1, DAYS):
    # If there is a flight on day d, then the pair (c[d-1], c[d]) must be one of allowed_flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 8. Compute day contributions for each city.
# On day 0, we add one credit for city c[0].
# For each subsequent day d (1 <= d < DAYS):
#   If there is no flight on day d, we add one credit to c[d].
#   If a flight occurs on day d, we add one credit both for c[d-1] and c[d].
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily_credits = []
    for d in range(1, DAYS):
        daily_credits.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily_credits))
    
# 9. Enforce required day credits for each city.
s.add(counts[0] == req[0])  # Split must have 6 days.
s.add(counts[1] == req[1])  # Santorini must have 7 days.
s.add(counts[2] == req[2])  # London must have 7 days.

# 10. Helper function: returns a Z3 expression that is True if on day d the itinerary includes a visit to city 'target'.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    # On a flight day, the day counts for both the previous and current city.
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 11. Event constraints: On day 12 and day 18 the itinerary must include Santorini (city 1) for the conference.
# Note: day 12 => index 11, day 18 => index 17.
s.add(inCityOnDay(11, 1))
s.add(inCityOnDay(17, 1))

# Finally, solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_out = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_out += f" (Flight: {dep} -> {arr})"
        print(day_out)
    
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
    
    print(f"\nFlight days: d1 = {m[d1]}, d2 = {m[d2]}")
else:
    print("No solution found")