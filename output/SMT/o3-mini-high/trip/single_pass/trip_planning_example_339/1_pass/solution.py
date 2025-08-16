from z3 import Solver, Int, And
import json

# We have 4 cities: Warsaw, Budapest, Paris, Riga.
# The traveler must spend:
# - 2 days in Warsaw (also for an annual show on days 1–2),
# - 7 days in Budapest,
# - 4 days in Paris,
# - 7 days in Riga (where a wedding is attended between day 11 and day 17).
#
# When flying from one city to the next on a given day, that day counts for both cities.
# Thus, if the itinerary spans 17 calendar days and the sum of required city-days is 2+7+4+7=20,
# then there must be exactly 20 - 17 = 3 flight days.
#
# We plan an ordering (and use only available direct flights):
#   Warsaw → Budapest → Paris → Riga
#
# Available flight routes:
#   Warsaw <-> Budapest, Warsaw <-> Riga, Warsaw <-> Paris,
#   Budapest <-> Paris, and Paris <-> Riga.
#
# In our ordering the flights take place on:
#   Flight1: Warsaw → Budapest (flight day d1)
#   Flight2: Budapest → Paris (flight day d2)
#   Flight3: Paris → Riga (flight day d3)
#
# When segmenting the itinerary, note that:
# - Days 1 through d1 will count for Warsaw.
# - Days d1 through d2 will count for Budapest.
# - Days d2 through d3 will count for Paris.
# - Days d3 through 17 will count for Riga.
#
# On a flight day the traveler “appears” in both the departure and arrival city.
#
# Let d1, d2, d3 be the flight days.
# Then the number of days accrued for each city is:
#   Warsaw:         d1 (days 1 to d1 inclusive) = 2     -->  d1 = 2.
#   Budapest:  (d2 - d1 + 1) = 7  --> d2 - 2 + 1 = 7  --> d2 = 8.
#   Paris:     (d3 - d2 + 1) = 4  --> d3 - 8 + 1 = 4  --> d3 = 11.
#   Riga:      (17 - d3 + 1) = 18 - d3 = 7  --> d3 = 11.
#
# Moreover, since the wedding in Riga must be between day 11 and day 17,
# and here the Riga segment is days 11–17, the constraint is met.
#
# Now we set up and solve the constraints with Z3.

# Create a Z3 solver instance.
s = Solver()

# Flight day variables (they are calendar days when flying occurs).
d1 = Int("d1")  # flight from Warsaw to Budapest
d2 = Int("d2")  # flight from Budapest to Paris
d3 = Int("d3")  # flight from Paris to Riga

# Basic ordering constraints on calendar days.
s.add(d1 >= 1, d1 < d2, d2 < d3, d3 <= 17)

# Add constraints based on required days in each city.
# Warsaw: Days 1 to d1 (inclusive) must total 2 days.
s.add(d1 == 2)
# Budapest: Days d1 to d2 (inclusive) must total 7 days.
s.add(d2 - d1 + 1 == 7)  # d2 - 2 + 1 == 7  --> d2 == 8
# Paris: Days d2 to d3 (inclusive) must total 4 days.
s.add(d3 - d2 + 1 == 4)  # d3 - 8 + 1 == 4  --> d3 == 11
# Riga: Days d3 to 17 (inclusive) must total 7 days.
s.add(18 - d3 == 7)      # 18 - d3 == 7  --> d3 == 11

# Wedding in Riga takes place between day 11 and day 17.
s.add(And(d3 >= 11, d3 <= 17))

# Check satisfiability and extract the flight days.
if s.check() == 'sat' or s.check().r == 1:
    m = s.model()
    flight1 = m[d1].as_long()  # expected to be 2
    flight2 = m[d2].as_long()  # expected to be 8
    flight3 = m[d3].as_long()  # expected to be 11
else:
    raise Exception("No solution found!")

# Build the itinerary day-by-day.
# On a flight day, we mark both departure and arrival cities.
# The route is:
#   Warsaw  (days 1 to d1)
#   flight on day d1: Warsaw and Budapest
#   Budapest (days d1+1 to d2-1)
#   flight on day d2: Budapest and Paris
#   Paris (days d2+1 to d3-1)
#   flight on day d3: Paris and Riga
#   Riga (days d3+1 to 17)
itinerary = []

for day in range(1, 18):
    if day == flight1:
        # Flight1 from Warsaw to Budapest on day d1.
        # On this day, the traveler is in both Warsaw and Budapest.
        itinerary.append({"day": day, "city": ["Warsaw", "Budapest"]})
    elif day == flight2:
        # Flight2 from Budapest to Paris on day d2.
        itinerary.append({"day": day, "city": ["Budapest", "Paris"]})
    elif day == flight3:
        # Flight3 from Paris to Riga on day d3.
        itinerary.append({"day": day, "city": ["Paris", "Riga"]})
    elif day < flight1:
        # Before the first flight, in Warsaw.
        itinerary.append({"day": day, "city": "Warsaw"})
    elif flight1 < day < flight2:
        # Between flight1 and flight2, in Budapest.
        itinerary.append({"day": day, "city": "Budapest"})
    elif flight2 < day < flight3:
        # Between flight2 and flight3, in Paris.
        itinerary.append({"day": day, "city": "Paris"})
    elif day > flight3:
        # After flight3, in Riga.
        itinerary.append({"day": day, "city": "Riga"})

# Optional: Check that each city gets the required total days (flight days count double).
def count_days(city, itinerary_list):
    total = 0
    for entry in itinerary_list:
        c = entry["city"]
        if isinstance(c, list):
            if city in c:
                total += 1  # count flight day for both cities
        else:
            if c == city:
                total += 1
    return total

assert count_days("Warsaw", itinerary) == 2
assert count_days("Budapest", itinerary) == 7
assert count_days("Paris", itinerary) == 4
assert count_days("Riga", itinerary) == 7

# Output the final itinerary as JSON.
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))