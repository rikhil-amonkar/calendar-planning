import json

# Input parameters
total_unique_days = 23
# There are 9 flights (which cause one overlapping day per flight) so the sum of city-day durations must equal:
# total_unique_days + num_flights = 23 + 9 = 32
# The required durations per city (in city-days) are:
city_durations = {
    "Berlin": 2,   # also wedding between day 1 and 2 (so Berlin must come first)
    "Milan": 3,
    "Seville": 3,
    "Paris": 5,
    "Lyon": 3,
    "Nice": 2,     # workshop between day 12 and 13 must be in Nice (Nice must include day 12 or 13)
    "Naples": 4,
    "Zurich": 5,
    "Stockholm": 3,  # annual show between day 20 and 22 (so Stockholm must cover days 20,21,22)
    "Riga": 2
}

# Direct flights between cities (bidirectional; provided as pairs):
direct_flights = [
    ("Paris", "Stockholm"),
    ("Seville", "Paris"),
    ("Naples", "Zurich"),
    ("Nice", "Riga"),
    ("Berlin", "Milan"),
    ("Paris", "Zurich"),
    ("Paris", "Nice"),
    ("Milan", "Paris"),
    ("Milan", "Riga"),
    ("Paris", "Lyon"),
    ("Milan", "Naples"),
    ("Paris", "Riga"),
    ("Berlin", "Stockholm"),
    ("Stockholm", "Riga"),
    ("Nice", "Zurich"),
    ("Milan", "Zurich"),
    ("Lyon", "Nice"),
    ("Zurich", "Stockholm"),
    ("Zurich", "Riga"),
    ("Berlin", "Naples"),
    ("Milan", "Stockholm"),
    ("Berlin", "Zurich"),
    ("Milan", "Seville"),
    ("Paris", "Naples"),
    ("Berlin", "Riga"),
    ("Nice", "Stockholm"),
    ("Berlin", "Paris"),
    ("Nice", "Naples")
]

# We must plan a route that visits all 10 cities with the given durations.
# One feasible ordering (found by trial ensuring flight connectivity and time constraints) is:
#   Berlin -> Milan -> Seville -> Paris -> Lyon -> Nice -> Naples -> Zurich -> Stockholm -> Riga
#
# Check direct flights along consecutive legs:
#   Berlin -> Milan         (present)
#   Milan -> Seville        (present, "Milan" and "Seville")
#   Seville -> Paris        (present)
#   Paris -> Lyon           (present)
#   Lyon -> Nice            (present)
#   Nice -> Naples          (present, "Nice and Naples")
#   Naples -> Zurich        (present, "Naples and Zurich")
#   Zurich -> Stockholm     (present, "Zurich and Stockholm")
#   Stockholm -> Riga       (present, "Stockholm and Riga")
#
# Also note:
# - Berlin is first so wedding on day 1-2 is satisfied.
# - Nice is visited with a 2-day block that (as we will schedule) covers day 12,13 matching the workshop.
# - Stockholm is given a 3-day block that will be scheduled to cover day 20-22.
#
# The total sum of city-day durations is 2+3+3+5+3+2+4+5+3+2 = 32.
# With 9 flights, the actual unique days on the timeline will be 32 - 9 = 23.
#
# We now fix a flight ordering.
itinerary_order = ["Berlin", "Milan", "Seville", "Paris", "Lyon", "Nice", "Naples", "Zurich", "Stockholm", "Riga"]

# We now compute the itinerary day ranges.
# In our model the traveler is present for each city's entire block.
# When flying on a day, that day is counted for both departing and arriving city.
# We assign “arrival” and “departure” days for each city block in a continuous timeline.
# In a standard contiguous schedule (flight always on the city block boundary),
# the relation is:
#    For the first city: start_day = 1 and end_day = start_day + duration - 1.
#    For every subsequent city, arrival_day = previous_city_end_day
#        and departure_day = arrival_day + duration - 1.
#
# However, with these fixed durations and 9 flights, the final departure day equals:
#    final_departure_day = 32 - 9 = 23.
#
# We compute the intervals accordingly.
itinerary = []
current_day = 1
for city in itinerary_order:
    duration = city_durations[city]
    # The city block covers days: current_day through current_day + duration - 1.
    start_day = current_day
    end_day = current_day + duration - 1
    itinerary.append({
        "day_range": f"{start_day}-{end_day}",
        "place": city
    })
    # For next city, the flight happens on the end_day (same day is counted for both cities),
    # so the next city's start day is the same as current end_day.
    current_day = end_day

# Because there are 9 flights, the unique timeline days are:
# last_day = itinerary[-1]['day_range'].split('-')[1] as integer.
# In our contiguous model, this computed final day equals 23.
# Let's verify:
final_day = current_day  # should be 23
if final_day != total_unique_days:
    raise ValueError("Itinerary timeline does not match total days constraint.")

# Verification of special constraints:
# - Berlin (first city) should cover day 1-2, which it does.
# - Nice (should cover day 12-13, including workshop interval [12,13])
# - Stockholm: we require the annual show between day 20 and 22.
#   In our computed itinerary, Stockholm gets day_range from Zurich's end_day to its own end_day.
#   Let's print the schedule for reference and note that with our contiguous assignment:
#       Berlin: 1-2
#       Milan: 2-4
#       Seville: 4-6
#       Paris: 6-10
#       Lyon: 10-12
#       Nice: 12-13
#       Naples: 13-16
#       Zurich: 16-20
#       Stockholm: 20-22      --> covers days 20,21,22 (annual show satisfied)
#       Riga: 22-23
#
# We now output the result as a JSON-formatted dictionary containing only day_range and place.

# Prepare the output as a list of day segments.
output = itinerary

print(json.dumps(output, indent=2))