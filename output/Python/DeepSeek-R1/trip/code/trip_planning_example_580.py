import itertools
import json

required_days = {
    "Paris": 6,
    "Porto": 7,
    "Reykjavik": 2
}
direct_flights = {
    "Geneva": ["Paris", "Oslo", "Porto"],
    "Paris": ["Geneva", "Oslo", "Porto", "Reykjavik"],
    "Porto": ["Paris", "Geneva", "Oslo"],
    "Reykjavik": ["Paris", "Oslo"],
    "Oslo": ["Paris", "Geneva", "Porto", "Reykjavik"]
}

remaining_cities = list(required_days.keys())
valid_sequence = None

for perm in itertools.permutations(remaining_cities):
    if perm[0] not in direct_flights["Geneva"]:
        continue
    valid = True
    for i in range(len(perm)-1):
        if perm[i+1] not in direct_flights[perm[i]]:
            valid = False
            break
    if not valid or "Oslo" not in direct_flights[perm[-1]]:
        continue
    
    current_day = 7
    day_usage = []
    for city in perm:
        duration = required_days[city]
        end = current_day + duration - 1
        day_usage.append(end)
        current_day = end
    if current_day != 19:
        continue
    
    valid_sequence = perm
    break

itinerary = [{"day_range": "Day 1-7", "place": "Geneva"}]
current_day = 7
for city in valid_sequence:
    duration = required_days[city]
    start = current_day
    end = start + duration - 1
    itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
    current_day = end
itinerary.append({"day_range": "Day 19-23", "place": "Oslo"})

print(json.dumps({"itinerary": itinerary}))