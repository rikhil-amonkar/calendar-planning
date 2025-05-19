#!/usr/bin/env python3
import json

# Input Parameters (constraints)
# Total trip days (accounting for overlaps on flight days): 20 days.
total_trip_days = 20

# Cities and required durations (in days, not counting that flight days are double‐counted)
# The sum of durations is 27. With 7 flight overlaps (between 8 cities), the effective trip length is 27 - 7 = 20.
durations = {
    "Bucharest": 2,  # visit relatives later in trip? (also check connectivity)
    "Barcelona": 3,
    "Stockholm": 4,
    "Reykjavik": 5,
    "Munich": 4,     # relatives in Munich must be between day 13 and 16 (inclusive in our plan)
    "Split": 3,
    "Oslo": 2,       # and the annual show is on day 16 to 17 (so Oslo must be exactly on these days)
    "Frankfurt": 4   # and the workshop is between day 17 and day 20
}

# Allowed direct flights given as undirected edges (both directions allowed)
allowed_flights = {
    frozenset(["Reykjavik", "Munich"]),
    frozenset(["Munich", "Frankfurt"]),
    frozenset(["Split", "Oslo"]),
    frozenset(["Reykjavik", "Oslo"]),
    frozenset(["Bucharest", "Munich"]),
    frozenset(["Oslo", "Frankfurt"]),
    frozenset(["Bucharest", "Barcelona"]),
    frozenset(["Barcelona", "Frankfurt"]),
    frozenset(["Reykjavik", "Frankfurt"]),
    frozenset(["Barcelona", "Stockholm"]),
    frozenset(["Barcelona", "Reykjavik"]),
    frozenset(["Stockholm", "Reykjavik"]),
    frozenset(["Barcelona", "Split"]),
    frozenset(["Bucharest", "Oslo"]),
    frozenset(["Bucharest", "Frankfurt"]),
    frozenset(["Split", "Stockholm"]),
    frozenset(["Barcelona", "Oslo"]),
    frozenset(["Stockholm", "Munich"]),
    frozenset(["Stockholm", "Oslo"]),
    frozenset(["Split", "Frankfurt"]),
    frozenset(["Barcelona", "Munich"]),
    frozenset(["Stockholm", "Frankfurt"]),
    frozenset(["Munich", "Oslo"]),
    frozenset(["Split", "Munich"])
}

# Chosen ordering:
# We have to arrange all 8 cities in an order such that:
# 1. The cumulative schedule fits exactly 20 days.
# 2. The specific constraints are satisfied:
#    - Oslo (2 days) must cover day 16-17 (annual show).
#    - Reykjavik (5 days) must cover day 9 to 13 to allow a friend meeting.
#    - Munich (4 days) must cover a day between 13 and 16 (for meeting relatives).
#    - Frankfurt (4 days) must cover days 17 to 20 (workshop).
# 3. All flights between successive cities are direct.
#
# After some algorithmic reasoning, one ordering that works is:
#   1. Bucharest (2 days)
#   2. Barcelona (3 days)
#   3. Stockholm (4 days)
#   4. Reykjavik (5 days)
#   5. Munich (4 days)
#   6. Split (3 days)
#   7. Oslo (2 days)
#   8. Frankfurt (4 days)
#
# Let’s check connectivity between successive cities:
# Bucharest -> Barcelona: allowed (Bucharest and Barcelona).
# Barcelona -> Stockholm: allowed (Barcelona and Stockholm).
# Stockholm -> Reykjavik: allowed (Stockholm and Reykjavik).
# Reykjavik -> Munich: allowed (Reykjavik and Munich).
# Munich -> Split: allowed (Split and Munich).
# Split -> Oslo: allowed (Split and Oslo).
# Oslo -> Frankfurt: allowed (Oslo and Frankfurt).
#
# Now, we compute the day ranges using the rule:
# If a city’s stay is from day X to Y and you fly on day Y to the next city,
# then that day Y is counted for both cities.
#
# Thus, for an ordered list with durations d1, d2, …, d8 the chaining is:
#   start_day[0] = 1
#   end_day[0] = start_day[0] + d1 - 1
#   For subsequent city i:
#       start_day[i] = end_day[i-1]   (flight day: counts for both cities)
#       end_day[i] = start_day[i] + d_i - 1
#
# With no waiting days, the final overall end day will be:
#   total = (sum of durations) - (number of flights)
# In our case: 27 - 7 = 20, as required.
ordered_cities = [
    "Bucharest",  # 2 days
    "Barcelona",  # 3 days
    "Stockholm",  # 4 days
    "Reykjavik",  # 5 days
    "Munich",     # 4 days (includes a day between 13 and 16)
    "Split",      # 3 days
    "Oslo",       # 2 days (must be day 16-17: we will see in schedule)
    "Frankfurt"   # 4 days (workshop, covering day 17-20)
]

# Verify that consecutive cities are connected by a direct flight.
def check_connections(order, flights):
    for i in range(len(order) - 1):
        if frozenset([order[i], order[i+1]]) not in flights:
            return False, order[i], order[i+1]
    return True, None, None

valid, cityA, cityB = check_connections(ordered_cities, allowed_flights)
if not valid:
    raise Exception(f"No direct flight between {cityA} and {cityB} in chosen ordering.")

# Compute the day ranges based on the chain rule
itinerary = []
current_day = 1
for city in ordered_cities:
    d = durations[city]
    start_day = current_day
    end_day = start_day + d - 1
    itinerary.append({
        "day_range": f"{start_day}-{end_day}",
        "place": city
    })
    # Next city starts on the day of flight, which is the same as this city's end day.
    current_day = end_day

# Since in the chaining the final city's end day is current_day, verify total trip days:
if current_day != total_trip_days:
    raise Exception(f"Computed itinerary ends on day {current_day} which does not equal the total trip days {total_trip_days}.")

# Check specific constraints in the computed itinerary:
# Find the itinerary item for Oslo and ensure its day range is "16-17"
oslo_segment = next(filter(lambda seg: seg["place"] == "Oslo", itinerary))
if oslo_segment["day_range"] != "16-17":
    raise Exception("Oslo segment does not match the required day range for the annual show (16-17).")

# Find Reykjavik and ensure its range covers days 9 to 13 (i.e. overlaps with 9-13)
reykjavik_segment = next(filter(lambda seg: seg["place"] == "Reykjavik", itinerary))
r_start, r_end = map(int, reykjavik_segment["day_range"].split('-'))
if not (r_start <= 9 <= r_end or r_start <= 13 <= r_end):
    raise Exception("Reykjavik segment does not cover the required friend meeting days between 9 and 13.")

# Munich relatives must be visited between day 13 and 16.
munich_segment = next(filter(lambda seg: seg["place"] == "Munich", itinerary))
m_start, m_end = map(int, munich_segment["day_range"].split('-'))
if not (m_start <= 13 <= m_end or m_start <= 16 <= m_end):
    raise Exception("Munich segment does not cover the required relatives meeting days between 13 and 16.")

# Frankfurt workshop must occur between day 17 and 20.
frankfurt_segment = next(filter(lambda seg: seg["place"] == "Frankfurt", itinerary))
f_start, f_end = map(int, frankfurt_segment["day_range"].split('-'))
if not (f_start <= 17 <= f_end or f_start <= 20 <= f_end):
    raise Exception("Frankfurt segment does not cover the required workshop days between 17 and 20.")

# Output the computed itinerary as JSON.
print(json.dumps(itinerary, indent=2))