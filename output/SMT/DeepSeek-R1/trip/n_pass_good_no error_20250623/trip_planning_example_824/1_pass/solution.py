import json

# Create the itinerary as per the hand-crafted plan
itinerary = []

# Berlin: Days 1-5 (first city)
itinerary.append({"day_range": "Day 1-5", "place": "Berlin"})
itinerary.append({"day_range": "Day 5", "place": "Berlin"})  # departure flight day

# Split: Days 5-7
itinerary.append({"day_range": "Day 5", "place": "Split"})    # arrival flight day
itinerary.append({"day_range": "Day 5-7", "place": "Split"})
itinerary.append({"day_range": "Day 7", "place": "Split"})    # departure flight day

# Lyon: Days 7-11
itinerary.append({"day_range": "Day 7", "place": "Lyon"})     # arrival flight day
itinerary.append({"day_range": "Day 7-11", "place": "Lyon"})
itinerary.append({"day_range": "Day 11", "place": "Lyon"})    # departure flight day

# Lisbon: Days 11-13
itinerary.append({"day_range": "Day 11", "place": "Lisbon"})  # arrival flight day
itinerary.append({"day_range": "Day 11-13", "place": "Lisbon"})
itinerary.append({"day_range": "Day 13", "place": "Lisbon"})  # departure flight day

# Bucharest: Days 13-15
itinerary.append({"day_range": "Day 13", "place": "Bucharest"})  # arrival flight day
itinerary.append({"day_range": "Day 13-15", "place": "Bucharest"})
itinerary.append({"day_range": "Day 15", "place": "Bucharest"})  # departure flight day

# Riga: Days 15-19
itinerary.append({"day_range": "Day 15", "place": "Riga"})    # arrival flight day
itinerary.append({"day_range": "Day 15-19", "place": "Riga"})
itinerary.append({"day_range": "Day 19", "place": "Riga"})    # departure flight day

# Tallinn: Days 19-22 (last city)
itinerary.append({"day_range": "Day 19", "place": "Tallinn"}) # arrival flight day
itinerary.append({"day_range": "Day 19-22", "place": "Tallinn"})

# Create the output dictionary
output = {"itinerary": itinerary}

# Convert to JSON
json_output = json.dumps(output, indent=2)
print(json_output)