from z3 import Int, Solver
import json

# We have 4 cities: Madrid, Seville, Paris, Bucharest.
# The itinerary is 15 days long.
# The requirements are:
#   - Madrid for 7 days and you must be in Madrid on days 1–7 (to attend a show).
#   - Seville for 3 days.
#   - Paris for 6 days.
#   - Bucharest for 2 days (with relatives visited between day 14 and day 15).
#
# When you take a flight on a day X from city A to city B, that same day X counts for both A and B.
#
# We are allowed direct flights between:
#   - Madrid and Seville
#   - Madrid and Paris
#   - Madrid and Bucharest
#   - Seville and Paris
#   - Paris and Bucharest
#   - Paris and Bucharest (or Bucharest and Paris) and also Paris and Bucharest as given,
#   - and Seville and Paris, Paris and Bucharest.
#
# Given the connectivity and the time‐requirements we choose the 
# only order that works is:
#    Segment 1: Madrid   (days: 1 ... flight day f1, counted as Madrid)
#    Segment 2: Seville  (from flight day f1 to flight day f2, counted on both flight days)
#    Segment 3: Paris    (from flight day f2 to flight day f3, counted on both flight days)
#    Segment 4: Bucharest(from flight day f3 to day 15)
#
# And since day X on which the flight occurs counts for both segments,
# the “city-days” in each segment are computed as:
#   Madrid:   days 1...f1         => count = f1
#   Seville:  days f1...f2        => count = f2 - f1 + 1
#   Paris:    days f2...f3        => count = f3 - f2 + 1
#   Bucharest:days f3...15        => count = 15 - f3 + 1
#
# The requirements are:
#   Madrid count == 7
#   Seville count == 3
#   Paris count == 6
#   Bucharest count == 2   (and this segment must cover days 14–15)
#
# A quick calculation shows that the flight days are uniquely determined:
#
#   For Madrid:  f1 = 7  (days 1..7, with day 7 a flight day that counts for Madrid)
#   For Seville: f2 - 7 + 1 = 3   -> f2 = 9   (so Seville is present on days 7,8,9)
#   For Paris:   f3 - 9 + 1 = 6   -> f3 = 14  (so Paris is present on days 9,10,11,12,13,14)
#   For Bucharest:15 - 14 + 1 = 2  (so Bucharest is on days 14,15)
#
# The flight transitions:
#   Day 7: Madrid -> Seville   (allowed: Madrid and Seville have direct flight)
#   Day 9: Seville -> Paris    (allowed: Seville and Paris have direct flight)
#   Day 14: Paris -> Bucharest (allowed: Paris and Bucharest have direct flight)
#
# Now we use Z3 to “solve” for the flight days.
# (In this simple case the arithmetic forces a unique solution.)
s = Solver()

f1 = Int("f1")  # Flight day from Madrid -> Seville
f2 = Int("f2")  # Flight day from Seville -> Paris
f3 = Int("f3")  # Flight day from Paris -> Bucharest

# Basic bounds: flight days must be within the 15-day schedule and in order.
s.add(f1 > 1, f1 < 15)
s.add(f2 > f1, f2 < 15)
s.add(f3 > f2, f3 <= 15)

# Duration constraints for each segment:
# Segment 1 (Madrid, days 1 to f1): count = f1 == 7 (must cover the Madrid show on days 1–7)
s.add(f1 == 7)
# Segment 2 (Seville, days f1 to f2): count = f2 - f1 + 1 == 3
s.add(f2 - f1 + 1 == 3)
# Segment 3 (Paris, days f2 to f3): count = f3 - f2 + 1 == 6
s.add(f3 - f2 + 1 == 6)
# Segment 4 (Bucharest, days f3 to 15): count = 15 - f3 + 1 == 2
s.add(15 - f3 + 1 == 2)

if s.check() == "sat" or s.check() == s.model():
    s.check()
    m = s.model()
    fl1 = m[f1].as_long()   # Expected to be 7
    fl2 = m[f2].as_long()   # Expected to be 9
    fl3 = m[f3].as_long()   # Expected to be 14

    # Fixed order: Madrid -> Seville -> Paris -> Bucharest
    seg1 = "Madrid"
    seg2 = "Seville"
    seg3 = "Paris"
    seg4 = "Bucharest"

    # Build the itinerary day-by-day.
    # If no flight on a day, then the traveler is only in one city.
    # On a flight day, the traveler is in both cities – the one leaving and the one arriving.
    itinerary = []
    for day in range(1, 16):
        cities = []
        if day < fl1:
            # Before the first flight day, only in Madrid.
            cities.append(seg1)
        elif day == fl1:
            # Flight day from Madrid to Seville: both cities count.
            cities.append(seg1)
            cities.append(seg2)
        elif day < fl2:
            # Between flight 1 and flight 2: exclusively in Seville.
            cities.append(seg2)
        elif day == fl2:
            # Flight day from Seville to Paris: both Seville and Paris.
            cities.append(seg2)
            cities.append(seg3)
        elif day < fl3:
            # Between flight 2 and flight 3: exclusively in Paris.
            cities.append(seg3)
        elif day == fl3:
            # Flight day from Paris to Bucharest: both Paris and Bucharest.
            cities.append(seg3)
            cities.append(seg4)
        else:
            # After the last flight: exclusively in Bucharest.
            cities.append(seg4)

        itinerary.append({"day": day, "places": cities})

    result = {"itinerary": itinerary}
    # Print the result as a formatted JSON string.
    print(json.dumps(result, indent=2))
else:
    print("No solution found")