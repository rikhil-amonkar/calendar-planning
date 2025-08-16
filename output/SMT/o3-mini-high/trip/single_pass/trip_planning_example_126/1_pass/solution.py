from z3 import Solver, Int, sat
import json

# We have three cities: Krakow, Paris, Seville.
# Requirements:
#   - Total trip length: 11 days.
#   - Days in Krakow: 5 days.
#   - Days in Paris: 2 days.
#   - Days in Seville: 6 days.
#   - When flying from one city to the next on a given day,
#     that day counts as being in both cities.
#   - Only direct flights available are between Krakow↔Paris and Paris↔Seville.
#   - Additionally, a workshop in Krakow must be attended between day 1 and day 5.
#
# Because the sum of the individual days is 5 + 2 + 6 = 13, but overlapping flight days
# count double, exactly 2 days must be “shared”. This forces an itinerary with exactly
# two flight days.
#
# A valid ordering that respects direct flights and the workshop time-window is:
#   Segment 1: Krakow, 5 days (Days 1 to 5). The workshop can be attended on, say, Day 3.
#   Segment 2: Paris, 2 days (Days 5 to 6; Day 5 is the flight day from Krakow to Paris).
#   Segment 3: Seville, 6 days (Days 6 to 11; Day 6 is the flight day from Paris to Seville).
#
# Note that on Day 5 you are in both Krakow and Paris, and on Day 6 in both Paris and Seville.

# We set up the decision variables as flight days:
#   flight1_day: Day on which we fly from Krakow to Paris.
#   flight2_day: Day on which we fly from Paris to Seville.
# By construction, the traveler starts in Krakow on Day 1 and ends the trip on Day 11.
solver = Solver()

# Define flight days (they are on the same day as the city change so counted for both segments)
flight1_day = Int('flight1_day')  # Flight from Krakow to Paris: must occur on the last day of Krakow's stay.
flight2_day = Int('flight2_day')  # Flight from Paris to Seville: must occur on the last day of Paris' stay.

# Constraint for Krakow:
# If the Krakow segment starts on day 1 and ends on flight1_day, then
# number of days in Krakow = flight1_day - 1 + 1 = flight1_day.
solver.add(flight1_day == 5)  # 5 days in Krakow

# Constraint for Paris:
# Paris segment runs from flight1_day (the day of flight from Krakow, counted in both cities)
# to flight2_day (the day of flight to Seville). Thus, days in Paris = flight2_day - flight1_day + 1.
solver.add(flight2_day - flight1_day + 1 == 2)  # 2 days in Paris

# Constraint for Seville:
# Seville segment runs from flight2_day (the day of flight from Paris, counted in both)
# to day 11 (the end of the trip). So days in Seville = 11 - flight2_day + 1.
solver.add(11 - flight2_day + 1 == 6)  # 6 days in Seville

# Ensure the flights occur in order.
solver.add(flight1_day < flight2_day)

# The workshop in Krakow must be attended between day 1 and day 5.
# Since the Krakow segment covers days 1 through flight1_day (which is 5),
# the workshop can be scheduled on any day within that interval.
# (For instance, the solver's solution implies Krakow occupies days 1-5, so day 3 is available.)

if solver.check() == sat:
    model = solver.model()
    f1 = model[flight1_day].as_long()  # Should be 5
    f2 = model[flight2_day].as_long()  # Should be 6

    # Build the itinerary day-by-day.
    # The idea: Each day (1 to 11) we include the city (or cities) in which the traveler is present.
    # During a flight day the traveler is considered to be in both the departure and arrival cities.
    itinerary = []
    for day in range(1, 12):
        cities = []
        # If day is in the Krakow segment (Days 1 to f1 inclusive)
        if day <= f1:
            cities.append("Krakow")
        # If day is in the Paris segment (from flight day from Krakow through flight day to Seville)
        if f1 <= day <= f2:
            cities.append("Paris")
        # If day is in the Seville segment (from flight day from Paris through day 11)
        if day >= f2:
            cities.append("Seville")
        itinerary.append({"day": day, "cities": cities})

    # Prepare the final JSON output.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=4))
else:
    print("No solution found")