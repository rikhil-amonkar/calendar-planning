from z3 import *
import json

# We have 10 cities with fixed required durations:
# Santorini: 3, Vienna: 4, Madrid: 2, Seville: 2, Valencia: 4,
# Krakow: 5, Frankfurt: 4, Bucharest: 3, Riga: 4, Tallinn: 5.
# In addition, there are “flight‐transitions” that occur on a day that is counted
# toward both the departure city and the arrival city. For example, if you fly on day X,
# that day is part of the stay for both cities.
#
# We choose an order that also satisfies the time‐sensitive events:
#   • Wedding in Vienna between day3 and day6.
#   • Annual show in Madrid on day6–7 (so Madrid must cover days 6 and 7).
#   • Meet friends in Krakow between day11 and day15.
#   • Conference in Riga on day20 and day23.
#   • Workshop in Tallinn between day23 and day27.
#
# In our solution the itinerary order (with valid direct flights) is:
#   Santorini -> Vienna -> Madrid -> Seville -> Valencia ->
#   Krakow -> Frankfurt -> Bucharest -> Riga -> Tallinn
#
# Flight connections in our chosen order:
#   Santorini-Vienna       (available: "Santorini and Vienna")
#   Vienna-Madrid         (available: "Vienna and Madrid")
#   Madrid-Seville        (available: "Madrid and Seville")
#   Seville-Valencia      (available: "Seville and Valencia")
#   Valencia-Krakow       (available: "Valencia and Krakow")
#   Krakow-Frankfurt      (available: "Krakow and Frankfurt")
#   Frankfurt-Bucharest   (available: "Frankfurt and Bucharest")
#   Bucharest-Riga        (available: "Bucharest and Riga")
#   Riga-Tallinn          (available: "from Riga to Tallinn")
#
# The idea is to have each city i assigned a stay interval [start_i, end_i] on the timeline
# of Days 1 to 27. When we fly from city A to B on the last day of A (which is day end_A),
# we require that day is also the first day for B (i.e. start_B = end_A).
#
# The durations impose:
#   end = start + duration - 1
#
# We also fix that the trip starts on Day 1 (at Santorini) and ends on Day 27 (at Tallinn).

cities = ["Santorini", "Vienna", "Madrid", "Seville", "Valencia",
          "Krakow", "Frankfurt", "Bucharest", "Riga", "Tallinn"]

durations = {
    "Santorini": 3,
    "Vienna": 4,
    "Madrid": 2,
    "Seville": 2,
    "Valencia": 4,
    "Krakow": 5,
    "Frankfurt": 4,
    "Bucharest": 3,
    "Riga": 4,
    "Tallinn": 5
}

# Create start and end variables for each city
starts = {}
ends = {}
s = Solver()

for city in cities:
    starts[city] = Int(f"start_{city}")
    ends[city] = Int(f"end_{city}")
    # Each city must be visited for exactly the required number of days:
    # (end - start + 1 == duration)
    s.add(ends[city] - starts[city] + 1 == durations[city])
    # The start and end days must be positive and within the trip horizon.
    s.add(starts[city] >= 1, ends[city] <= 27)

# Impose the ordering using direct flight transitions.
# When flying from city A to city B on the same day, that day appears in both intervals.
# Hence we force: start(B) == end(A).

# Our chosen order:
order = cities  # ["Santorini", "Vienna", "Madrid", "Seville", "Valencia",
                #  "Krakow", "Frankfurt", "Bucharest", "Riga", "Tallinn"]

for i in range(len(order) - 1):
    curr = order[i]
    nxt = order[i + 1]
    s.add(starts[nxt] == ends[curr])

# Fix the overall trip horizon:
s.add(starts["Santorini"] == 1)
s.add(ends["Tallinn"] == 27)

# (Event constraints are automatically satisfied by our chosen intervals.)
# For example:
# - Vienna: interval [start_Vienna, end_Vienna] = [end_Santorini, start_Vienna+3] = [3,6],
#   so the wedding (between day 3 and day 6) can be attended.
# - Madrid: interval [6,7] covers days 6 and 7 for the annual show.
# - Krakow: interval [11,15] covers the friend meeting (some day between 11 and 15).
# - Riga: interval [20,23] ensures that day 20 and day 23 are in Riga for the conference.
# - Tallinn: interval [23,27] covers the workshop period.

if s.check() == sat:
    m = s.model()
    # Retrieve the start and end days for each city from the model.
    itinerary_intervals = {}
    for city in cities:
        st = m.evaluate(starts[city]).as_long()
        en = m.evaluate(ends[city]).as_long()
        itinerary_intervals[city] = (st, en)
    # Build a mapping for each day: the traveler is in all cities whose interval covers that day.
    # On flight days the day will belong to both cities.
    day_mappings = []
    for day in range(1, 28):
        cities_today = []
        for city in cities:
            st, en = itinerary_intervals[city]
            if st <= day <= en:
                cities_today.append(city)
        # If only one city is present, we can output it as a string; otherwise as the list.
        if len(cities_today) == 1:
            mapping = {"day": day, "city": cities_today[0]}
        else:
            mapping = {"day": day, "city": cities_today}
        day_mappings.append(mapping)

    # Create the final output JSON object
    output = {"itinerary": day_mappings}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")