#!/usr/bin/env python3
import json

# Trip constraints and input variables
total_days = 16
# Required days in each city (non-overlapped total durations)
london_required = 7   # Also visit relatives between Day 1 and Day 7
split_required = 5    # Must attend annual show from Day 7 to Day 11 in Split
oslo_required = 2
porto_required = 5

# Direct flight connections (both directions are allowed)
direct_flights = {
    ("London", "Oslo"), ("Oslo", "London"),
    ("Split", "Oslo"), ("Oslo", "Split"),
    ("Oslo", "Porto"), ("Porto", "Oslo"),
    ("London", "Split"), ("Split", "London")
}

def valid_flight(from_city, to_city):
    return (from_city, to_city) in direct_flights

# The itinerary must visit four cities.
# Given the constraints (London relatives early; show in Split on Day 7-11)
# and the available direct flights, the only possible order is:
# London -> Split -> Oslo -> Porto
route = ["London", "Split", "Oslo", "Porto"]

# Validate that required consecutive flights exist in the route.
if not (valid_flight("London", "Split") and valid_flight("Split", "Oslo") and valid_flight("Oslo", "Porto")):
    print(json.dumps({"error": "No valid route found given the flight connections."}))
    exit(1)

# The sum of required days if there were no flight overlaps:
# 7 (London) + 5 (Split) + 2 (Oslo) + 5 (Porto) = 19 days.
# Since the total trip duration is 16 days, we need exactly 3 overlapping flight days.
# The flight rule is: if you fly on day X then that day counts for both departure and arrival.
# Thus, we choose the flight days to be:
#   Flight from London->Split on Day 7 (London covers Day 1-7, Split covers Day 7-11)
#   Flight from Split->Oslo on Day 11 (Split covers Day 7-11, Oslo covers Day 11-12)
#   Flight from Oslo->Porto on Day 12 (Oslo covers Day 11-12, Porto covers Day 12-16)

itinerary = []
current_day = 1

# London segment: from Day 1 to Day 7
london_start = current_day
london_end = london_start + london_required - 1  # 1 + 7 - 1 = 7
itinerary.append({
    "day_range": f"Day {london_start}-{london_end}",
    "place": "London"
})
# Flight from London to Split on Day 7 (overlap on Day 7)
current_day = london_end  # current_day remains 7 for arrival in Split

# Split segment: must cover the annual show from Day 7 to Day 11
split_start = current_day  # 7 (flight day counts for both cities)
split_end = split_start + split_required - 1  # 7 + 5 - 1 = 11
itinerary.append({
    "day_range": f"Day {split_start}-{split_end}",
    "place": "Split"
})
# Flight from Split to Oslo on Day 11 (overlap on Day 11)
current_day = split_end  # current_day becomes 11 for arrival in Oslo

# Oslo segment: 2 days, with flight overlap on Day 11
oslo_start = current_day  # 11
oslo_end = oslo_start + oslo_required - 1  # 11 + 2 - 1 = 12
itinerary.append({
    "day_range": f"Day {oslo_start}-{oslo_end}",
    "place": "Oslo"
})
# Flight from Oslo to Porto on Day 12 (overlap on Day 12)
current_day = oslo_end  # current_day becomes 12 for arrival in Porto

# Porto segment: from Day 12 to Day 16
porto_start = current_day  # 12
porto_end = porto_start + porto_required - 1  # 12 + 5 - 1 = 16
itinerary.append({
    "day_range": f"Day {porto_start}-{porto_end}",
    "place": "Porto"
})

# Final check: the last day should equal the total trip days
if porto_end != total_days:
    print(json.dumps({"error": "The computed itinerary does not match the total trip duration."}))
    exit(1)

# Output the itinerary as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output))