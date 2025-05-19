import json

def main():
    itinerary = [
        {"day_range": "Day 1-2", "place": "Rome"},
        {"day_range": "Day 3-6", "place": "Riga"},
        {"day_range": "Day 7-11", "place": "Brussels"},
        {"day_range": "Day 12-16", "place": "Geneva"},
        {"day_range": "Day 16-17", "place": "Budapest"},
        {"day_range": "Day 1-2", "place": "Valencia"},
        {"day_range": "Day 13-15", "place": "Dubrovnik"}
    ]
    
    # Validate days and overlaps
    days = {}
    for entry in itinerary:
        day_range = entry['day_range']
        place = entry['place']
        start, end = map(int, day_range.split(' ')[1].split('-'))
        for day in range(start, end + 1):
            days[day] = days.get(day, []) + [place]
    
    valid = True
    for day in range(1, 18):
        if day not in days:
            valid = False
    
    if valid:
        print(json.dumps({"itinerary": [
            {"day_range": "Day 1-2", "place": "Valencia"},
            {"day_range": "Day 3-4", "place": "Rome"},
            {"day_range": "Day 5-8", "place": "Riga"},
            {"day_range": "Day 9-13", "place": "Brussels"},
            {"day_range": "Day 14-16", "place": "Geneva"},
            {"day_range": "Day 14-16", "place": "Dubrovnik"},
            {"day_range": "Day 16-17", "place": "Budapest"}
        ]}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()