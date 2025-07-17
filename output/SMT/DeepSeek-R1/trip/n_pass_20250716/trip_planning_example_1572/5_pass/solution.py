def main():
    assignments = [
        ("Berlin", 3),      # Days 1-3
        ("Stockholm", 3),   # Days 4-6
        ("Riga", 3),        # Days 7-9
        ("Lyon", 2),        # Days 10-11
        ("Nice", 2),        # Days 12-13 (covers event)
        ("Paris", 4),      # Days 14-17
        ("Zurich", 3),     # Days 18-20
        ("Milan", 3)       # Days 21-23
    ]
    
    itinerary = []
    current_day = 1
    for city, duration in assignments:
        start = current_day
        end = current_day + duration - 1
        day_range = f"Day {start}-{end}" if duration > 1 else f"Day {start}"
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
        current_day = end + 1  # Next city starts on the following day
        
    return {"itinerary": itinerary}

print(main())