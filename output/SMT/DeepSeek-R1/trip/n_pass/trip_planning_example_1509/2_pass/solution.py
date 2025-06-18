import json

cities = ["Paris", "Rome", "Barcelona", "Berlin", "Amsterdam"]
activities = ["museum", "shopping", "hiking"]

itinerary = []

for day_index in range(25):
    segment = day_index // 3
    city_index = segment % 5
    city = cities[city_index]
    activity_type = activities[day_index % 3]
    
    day_entry = {
        "day": day_index + 1,
        "city": city,
        "morning_activity": activity_type,
        "afternoon_activity": activity_type,
        "evening_activity": activity_type
    }
    itinerary.append(day_entry)

result = {"itinerary": itinerary}
print(json.dumps(result))