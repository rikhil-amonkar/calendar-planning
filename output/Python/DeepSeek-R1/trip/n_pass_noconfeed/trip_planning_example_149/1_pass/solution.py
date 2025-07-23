import json

def main():
    total_days = 10
    london_days = 3
    santorini_days = 6
    istanbul_days = 3
    
    non_travel_istanbul_end = istanbul_days - 1
    segments = []
    
    if non_travel_istanbul_end >= 1:
        if non_travel_istanbul_end == 1:
            day_range_str = "Day 1"
        else:
            day_range_str = f"Day 1-{non_travel_istanbul_end}"
        segments.append({"day_range": day_range_str, "place": "Istanbul"})
    
    travel_day1 = non_travel_istanbul_end + 1
    segments.append({"day_range": f"Day {travel_day1}", "place": "Istanbul and London"})
    
    non_travel_london_days = london_days - 2
    if non_travel_london_days > 0:
        london_non_travel_start = travel_day1 + 1
        london_non_travel_end = london_non_travel_start + non_travel_london_days - 1
        if london_non_travel_start == london_non_travel_end:
            segments.append({"day_range": f"Day {london_non_travel_start}", "place": "London"})
        else:
            segments.append({"day_range": f"Day {london_non_travel_start}-{london_non_travel_end}", "place": "London"})
        next_day = london_non_travel_end + 1
    else:
        next_day = travel_day1 + 1
    
    travel_day2 = next_day
    segments.append({"day_range": f"Day {travel_day2}", "place": "London and Santorini"})
    
    santorini_non_travel_start = travel_day2 + 1
    santorini_non_travel_end = total_days
    if santorini_non_travel_start <= santorini_non_travel_end:
        if santorini_non_travel_start == santorini_non_travel_end:
            segments.append({"day_range": f"Day {santorini_non_travel_start}", "place": "Santorini"})
        else:
            segments.append({"day_range": f"Day {santorini_non_travel_start}-{santorini_non_travel_end}", "place": "Santorini"})
    
    result = {"itinerary": segments}
    print(json.dumps(result))

if __name__ == "__main__":
    main()