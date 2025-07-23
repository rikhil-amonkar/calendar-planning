# Define the sequence of cities and their respective start days
sequence = [
    ("Munich", 4),
    ("Venice", 7),
    ("Santorini", 10),
    ("Manchester", 13),
    ("Porto", 16),
    ("Valencia", 14),
    ("Bucharest", 16),
    ("Tallinn", 21),
    ("Vienna", 19)
]

# Create a dictionary to store the start days for each city
start_days = {city: start for city, start in sequence}

# Create a list to store the itinerary
itinerary = []

# Populate the itinerary
for city, start in sequence:
    duration = cities[city]
    for day in range(start, start + duration):
        itinerary.append({"day": day, "city": city})

# Sort the itinerary by day
itinerary.sort(key=lambda x: x["day"])

# Print the itinerary
result = {"itinerary": itinerary}
print(result)