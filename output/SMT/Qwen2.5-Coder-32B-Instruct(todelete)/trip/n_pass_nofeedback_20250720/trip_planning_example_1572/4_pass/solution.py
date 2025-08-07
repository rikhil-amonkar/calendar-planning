# Define the manual itinerary
itinerary = [
    {"day": 1, "city": "Berlin"},
    {"day": 2, "city": "Berlin"},
    {"day": 3, "city": "Milan"},
    {"day": 4, "city": "Milan"},
    {"day": 5, "city": "Paris"},
    {"day": 6, "city": "Paris"},
    {"day": 7, "city": "Paris"},
    {"day": 8, "city": "Paris"},
    {"day": 9, "city": "Paris"},
    {"day": 10, "city": "Lyon"},
    {"day": 11, "city": "Lyon"},
    {"day": 12, "city": "Lyon"},
    {"day": 12, "city": "Nice"},
    {"day": 13, "city": "Nice"},
    {"day": 14, "city": "Zurich"},
    {"day": 15, "city": "Zurich"},
    {"day": 16, "city": "Zurich"},
    {"day": 17, "city": "Zurich"},
    {"day": 18, "city": "Zurich"},
    {"day": 18, "city": "Stockholm"},
    {"day": 19, "city": "Stockholm"},
    {"day": 20, "city": "Stockholm"},
    {"day": 21, "city": "Naples"},
    {"day": 22, "city": "Naples"},
    {"day": 22, "city": "Seville"},
    {"day": 23, "city": "Seville"}
]

# Remove duplicate entries (days counted for both cities)
final_itinerary = []
for i in range(len(itinerary)):
    if i == 0 or itinerary[i] != itinerary[i-1]:
        final_itinerary.append(itinerary[i])

# Convert to the required JSON format
result = {"itinerary": final_itinerary}
print(result)