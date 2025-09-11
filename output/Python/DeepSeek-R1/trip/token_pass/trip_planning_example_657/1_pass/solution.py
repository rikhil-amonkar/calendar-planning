import json
from collections import defaultdict

def main():
    # Define the moves: each tuple is (day, from_city, to_city)
    # None for to_city means no travel that day (stay in from_city)
    moves = [
        (1, "Naples", "Valencia"),
        (2, "Valencia", None),
        (3, "Valencia", None),
        (4, "Valencia", "Naples"),
        (5, "Naples", None),
        (6, "Naples", "Manchester"),
        (7, "Manchester", None),
        (8, "Manchester", None),
        (9, "Manchester", "Oslo"),
        (10, "Oslo", None),
        (11, "Oslo", None),
        (12, "Oslo", "Vilnius"),
        (13, "Vilnius", "Frankfurt"),
        (14, "Frankfurt", None),
        (15, "Frankfurt", None),
        (16, "Frankfurt", None)
    ]
    
    # Create a dictionary to collect days for each city
    city_days = defaultdict(list)
    
    for day, from_city, to_city in moves:
        city_days[from_city].append(day)
        if to_city is not None:
            city_days[to_city].append(day)
    
    # Sort the days for each city
    for city in city_days:
        city_days[city].sort()
    
    # Group consecutive days into ranges for each city
    itinerary_list = []
    for city, days in city_days.items():
        days = sorted(set(days))  # Ensure unique and sorted
        if not days:
            continue
        ranges = []
        start = days[0]
        prev = days[0]
        for current in days[1:]:
            if current != prev + 1:
                ranges.append((start, prev))
                start = current
            prev = current
        ranges.append((start, prev))
        
        for start_day, end_day in ranges:
            if start_day == end_day:
                day_range_str = f"Day {start_day}"
            else:
                day_range_str = f"Day {start_day}-{end_day}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
    
    # Sort itinerary by the first day of each range
    itinerary_list.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0])
    
    # Output as JSON
    result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()