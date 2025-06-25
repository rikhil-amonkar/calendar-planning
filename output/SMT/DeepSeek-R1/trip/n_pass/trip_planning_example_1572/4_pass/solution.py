def main():
    assignments = [
        ("Berlin", 3),      # Days 1-3
        ("Milan", 2),       # Days 4-5
        ("Zurich", 3),      # Days 6-8
        ("Lyon", 3),        # Days 9-11
        ("Nice", 2),        # Days 12-13 (event covered)
        ("Paris", 4),       # Days 14-17
        ("Stockholm", 3),   # Days 18-20
        ("Riga", 3)         # Days 21-23
    ]
    
    itinerary = []
    start_day = 1
    for city, days in assignments:
        end_day = start_day + days - 1
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({
            "day_range": day_range_str,
            "place": city
        })
        start_day = end_day + 1
        
    result = {"itinerary": itinerary}
    return result

print(main())