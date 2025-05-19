import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

start_nob = 9 * 60
travel_to_presidio = 17
robert_start = 11 * 60 + 15
robert_end = 17 * 60 + 45

arrival_presidio = start_nob + travel_to_presidio
meet_start = max(arrival_presidio, robert_start)
meet_end = robert_end

itinerary = []
if meet_end - meet_start >= 120:
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Robert",
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    })

print(json.dumps({"itinerary": itinerary}, indent=2))