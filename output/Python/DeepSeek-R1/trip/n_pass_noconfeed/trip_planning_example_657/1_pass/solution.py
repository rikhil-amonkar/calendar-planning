import json

def main():
    total_days = 16
    city_durations = {
        "Frankfurt": 4,
        "Manchester": 4,
        "Valencia": 4,
        "Naples": 4,
        "Oslo": 3,
        "Vilnius": 2
    }
    city_order = ["Valencia", "Naples", "Manchester", "Oslo", "Vilnius", "Frankfurt"]
    
    start_day = 1
    itinerary = []
    for city in city_order:
        duration = city_durations[city]
        end_day = start_day + duration - 1
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range_str, "place": city})
        start_day = end_day
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()