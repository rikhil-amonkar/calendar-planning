#!/usr/bin/env python3
import json

# Input parameters (all durations in days)
# Each city must be visited with the following total allocated days.
durations = {
    "Dublin": 5,
    "Vienna": 2,
    "Helsinki": 3,
    "Riga": 3,
    "Reykjavik": 2,
    "Tallinn": 5
}

# Event constraints:
# - In Vienna, an annual show occurs between day 2 and day 3,
#   so the Vienna visit must cover both day 2 and day 3.
# - In Helsinki, you want to meet your friends between day 3 and 5,
#   so the Helsinki visit must cover at least one day within that range.
# - In Tallinn, there is a wedding between day 7 and day 11,
#   so the Tallinn visit must include at least one day in that window.
#
# Direct flights exist between certain cities.
# We will choose an itinerary order that uses only those direct flights.
#
# One valid order that meets all constraints is:
#
#   Segment 1: Reykjavik (2 days)
#   Segment 2: Vienna (2 days)  --> must cover day2 and day3
#   Segment 3: Helsinki (3 days) --> must cover some day between 3 and 5
#   Segment 4: Dublin (5 days)
#   Segment 5: Riga (3 days)
#   Segment 6: Tallinn (5 days)  --> must cover some day between 7 and 11 (here day 11)
#
# Check direct flight connections based on the given list:
#  - Reykjavik <--> Vienna         (exists)
#  - Vienna <--> Helsinki          (exists)
#  - Helsinki <--> Dublin          (exists)
#  - Dublin <--> Riga              (exists)
#  - Riga --> Tallinn              (exists)
#
# The total allocated days sum is 2+2+3+5+3+5 = 20. Since on each flight day the traveler
# is counted in both the departure and arrival city, the total calendar days used is
# 20 - (number of transitions) = 20 - 5 = 15, as required.

# Define the chosen itinerary order as a list of (city, allocated_days) tuples.
itinerary_order = [
    ("Reykjavik", durations["Reykjavik"]),
    ("Vienna", durations["Vienna"]),
    ("Helsinki", durations["Helsinki"]),
    ("Dublin", durations["Dublin"]),
    ("Riga", durations["Riga"]),
    ("Tallinn", durations["Tallinn"])
]

# Compute the day ranges.
# The rule: If you fly from city A to city B on day X, that day is counted in both cities.
# Let s_i be the start day of segment i and e_i be the end day.
# For the first city, s_1 = 1 and e_1 = d1.
# For subsequent segments, s_i = previous segment's end day
# and e_i = s_i + d_i - 1.
# Because the flight overlaps the last day of the previous segment and the first day of the next.
itinerary = []
current_day = 1
for city, dur in itinerary_order:
    start_day = current_day
    end_day = start_day + dur - 1
    itinerary.append({
        "day_range": f"{start_day}-{end_day}",
        "place": city
    })
    # The next segment starts on the end_day (overlap flight day)
    current_day = end_day

# At the end, the final day should be 15.
final_day = current_day
if final_day != 15:
    raise ValueError(f"Calculated itinerary length is {final_day} days, expected 15 days.")

# Now check that event constraints are satisfied.
def day_in_range(day_range, target_range):
    # day_range and target_range are strings like "start-end"
    start, end = map(int, day_range.split('-'))
    tstart, tend = target_range
    # Check if there's any day in [start, end] that lies within [tstart, tend]
    return not (end < tstart or start > tend)

# Vienna must cover days 2 and 3.
vienna_range = next(item["day_range"] for item in itinerary if item["place"] == "Vienna")
# We require that both day 2 and day 3 are in Vienna's range.
vienna_start, vienna_end = map(int, vienna_range.split('-'))
if not (vienna_start <= 2 <= vienna_end and vienna_start <= 3 <= vienna_end):
    raise ValueError("Vienna itinerary does not cover the annual show days (2-3).")

# Helsinki must cover at least one day between day 3 and day 5.
helsinki_range = next(item["day_range"] for item in itinerary if item["place"] == "Helsinki")
if not day_in_range(helsinki_range, (3, 5)):
    raise ValueError("Helsinki itinerary does not cover the friend meeting window (3-5).")

# Tallinn must cover at least one day between day 7 and day 11.
tallinn_range = next(item["day_range"] for item in itinerary if item["place"] == "Tallinn")
if not day_in_range(tallinn_range, (7, 11)):
    raise ValueError("Tallinn itinerary does not cover the wedding window (7-11).")

# Output the itinerary as a JSON-formatted dictionary.
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))