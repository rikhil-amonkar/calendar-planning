import json

total_days = 16
lyon_stay = 7
bucharest_stay = 7
porto_stay = 4

bucharest_start = 1
bucharest_end = bucharest_start + bucharest_stay - 1
lyon_start = bucharest_end
lyon_end = lyon_start + lyon_stay - 1
porto_start = lyon_end
porto_end = porto_start + porto_stay - 1

itinerary = [
    {"day_range": f"Day {bucharest_start}-{bucharest_end}", "place": "Bucharest"},
    {"day_range": f"Day {lyon_start}-{lyon_end}", "place": "Lyon"},
    {"day_range": f"Day {porto_start}-{porto_end}", "place": "Porto"}
]

result = {"itinerary": itinerary}
print(json.dumps(result))