import json

# Define constraints
london_days = 3
santorini_days = 6
istanbul_days = 3
total_days = 10
conference_days = {5, 10}

# Calculate Santorini segment
santorini_start = min(conference_days)
santorini_end = santorini_start + santorini_days - 1

# Calculate London segment
london_end = santorini_start
london_start = london_end - london_days + 1

# Calculate Istanbul segment
istanbul_end = london_start
istanbul_start = istanbul_end - istanbul_days + 1

# Validate all constraints are met
assert santorini_end == max(conference_days), "Conference day mismatch"
assert (london_end - london_start + 1) == london_days, "London days mismatch"
assert (istanbul_end - istanbul_start + 1) == istanbul_days, "Istanbul days mismatch"

# Build itinerary
itinerary = []

istanbul_range = f"Day {istanbul_start}-{istanbul_end}" if istanbul_start != istanbul_end else f"Day {istanbul_start}"
itinerary.append({"day_range": istanbul_range, "place": "Istanbul"})

london_range = f"Day {london_start}-{london_end}" if london_start != london_end else f"Day {london_start}"
itinerary.append({"day_range": london_range, "place": "London"})

santorini_range = f"Day {santorini_start}-{santorini_end}" if santorini_start != santorini_end else f"Day {santorini_start}"
itinerary.append({"day_range": santorini_range, "place": "Santorini"})

# Output result
print(json.dumps({"itinerary": itinerary}))