import json

# Input parameters
total_days = 18
split_days = 6
santorini_days = 7
london_days = 7
conference_start = 12
conference_end = 18

# Calculate Split segment
split_start = 1
split_end = split_start + split_days - 1

# Calculate London segment (must end at conference_start)
london_start = split_end
london_end = london_start + london_days - 1

# Calculate Santorini segment
santorini_start = conference_start
santorini_end = conference_end

# Build itinerary
itinerary = []
itinerary.append({"day_range": f"Day {split_start}-{split_end}", "place": "Split"})
itinerary.append({"day_range": f"Day {london_start}-{london_end}", "place": "London"})
itinerary.append({"day_range": f"Day {santorini_start}-{santorini_end}", "place": "Santorini"})

# Output result
print(json.dumps({"itinerary": itinerary}))