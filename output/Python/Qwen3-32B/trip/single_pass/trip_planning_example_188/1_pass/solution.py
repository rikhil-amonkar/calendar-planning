import json

# Define input parameters based on the problem constraints
brussels_days = 2
split_days = 5
barcelona_days = 7
total_days = 12

# Initialize itinerary list
itinerary = []

# Calculate day ranges for each city
# Brussels: starts on day 1, ends on day 2
brussels_start = 1
brussels_end = brussels_start + brussels_days - 1
itinerary.append({
    "day_range": f"Day {brussels_start}-{brussels_end}",
    "place": "Brussels"
})

# Barcelona: starts on the same day as Brussels ends (day 2), lasts 7 days
barcelona_start = brussels_end
barcelona_end = barcelona_start + barcelona_days - 1
itinerary.append({
    "day_range": f"Day {barcelona_start}-{barcelona_end}",
    "place": "Barcelona"
})

# Split: starts on the same day as Barcelona ends (day 8), lasts 5 days
split_start = barcelona_end
split_end = split_start + split_days - 1
itinerary.append({
    "day_range": f"Day {split_start}-{split_end}",
    "place": "Split"
})

# Construct and print the JSON result
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))