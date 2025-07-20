def main():
    assignments = [
        ("Berlin", 4),
        ("Stockholm", 4),
        ("Riga", 3),
        ("Nice", 2),
        ("Zurich", 3),
        ("Milan", 3),
        ("Lyon", 2),
        ("Paris", 2)
    ]
    
    itinerary = []
    start_day = 1
    for city, days in assignments:
        end_day = start_day + days - 1
        if days == 1:
            day_range_str = f"Day {start_day}"
        else:
            day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({
            "day_range": day_range_str,
            "place": city
        })
        start_day = end_day + 1
        
    result = {"itinerary": itinerary}
    return result

print(main())