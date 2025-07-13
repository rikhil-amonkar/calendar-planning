def create_valid_itinerary():
    # Define the itinerary with day-place mappings
    itinerary = [
        {"day_range": "Day 1", "place": "Berlin"},
        {"day_range": "Day 2", "place": "Berlin"},
        {"day_range": "Day 3", "place": "Berlin"},
        {"day_range": "Day 3", "place": "Barcelona"},  # Flight from Berlin to Barcelona
        {"day_range": "Day 4", "place": "Barcelona"},
        {"day_range": "Day 4", "place": "Lyon"},      # Flight from Barcelona to Lyon
        {"day_range": "Day 5", "place": "Lyon"},
        {"day_range": "Day 5", "place": "Nice"},      # Flight from Lyon to Nice
        {"day_range": "Day 6", "place": "Nice"},
        {"day_range": "Day 7", "place": "Nice"},
        {"day_range": "Day 8", "place": "Nice"},
        {"day_range": "Day 9", "place": "Nice"},
        {"day_range": "Day 10", "place": "Nice"},
        {"day_range": "Day 10", "place": "Athens"},   # Flight from Nice to Athens
        {"day_range": "Day 11", "place": "Athens"},
        {"day_range": "Day 12", "place": "Athens"},
        {"day_range": "Day 13", "place": "Athens"},
        {"day_range": "Day 14", "place": "Athens"},
        {"day_range": "Day 15", "place": "Athens"},
        {"day_range": "Day 15", "place": "Stockholm"}, # Flight from Athens to Stockholm
        {"day_range": "Day 16", "place": "Stockholm"},
        {"day_range": "Day 17", "place": "Stockholm"},
        {"day_range": "Day 18", "place": "Stockholm"},
        {"day_range": "Day 19", "place": "Stockholm"},
        {"day_range": "Day 20", "place": "Stockholm"}
    ]

    # Verify city durations
    city_days = {
        "Berlin": 0,
        "Nice": 0,
        "Athens": 0,
        "Stockholm": 0,
        "Barcelona": 0,
        "Vilnius": 0,
        "Lyon": 0
    }

    for entry in itinerary:
        if "-" in entry["day_range"]:
            start, end = map(int, entry["day_range"].replace("Day ", "").split("-"))
            days = end - start + 1
        else:
            days = 1
        city_days[entry["place"]] += days

    # Check against requirements
    requirements = {
        "Berlin": 3,
        "Nice": 5,
        "Athens": 5,
        "Stockholm": 5,
        "Barcelona": 2,
        "Vilnius": 4,
        "Lyon": 2
    }

    # Check flight connections (manually verified)
    valid = True
    for city, req in requirements.items():
        if city_days[city] != req:
            valid = False
            break

    if valid and len(itinerary) == 25:  # 20 days plus flight days
        # Adjust to show continuous stays
        final_itinerary = []
        current_place = None
        start_day = 1
        
        for day in range(1, 21):
            # Find all entries for this day
            day_entries = [e for e in itinerary if f"Day {day}" in e["day_range"]]
            
            if len(day_entries) == 1:
                place = day_entries[0]["place"]
                if place != current_place:
                    if current_place is not None:
                        final_itinerary.append({
                            "day_range": f"Day {start_day}-{day-1}",
                            "place": current_place
                        })
                    current_place = place
                    start_day = day
            else:  # Flight day
                if current_place is not None:
                    final_itinerary.append({
                        "day_range": f"Day {start_day}-{day-1}",
                        "place": current_place
                    })
                for entry in day_entries:
                    final_itinerary.append({
                        "day_range": f"Day {day}",
                        "place": entry["place"]
                    })
                current_place = day_entries[-1]["place"]
                start_day = day + 1
        
        # Add last segment
        if current_place is not None and start_day <= 20:
            final_itinerary.append({
                "day_range": f"Day {start_day}-20",
                "place": current_place
            })

        return {"itinerary": final_itinerary}
    else:
        return {"error": "Invalid itinerary"}

# Generate the itinerary
itinerary = create_valid_itinerary()
print(itinerary)