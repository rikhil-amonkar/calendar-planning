import json

def plan_itinerary():
    # Fixed constraints
    total_days = 16
    cities = {
        "Seville": 4,
        "Rome": 3,
        "Istanbul": 2,
        "Naples": 7,
        "Santorini": 4
    }
    
    # Special date constraints
    istanbul_fixed = (6, 7)  # must be in Istanbul on day 6 and 7
    santorini_fixed = (13, 16)  # must be in Santorini on days 13-16
    
    # Direct flights graph
    flights = {
        "Seville": ["Rome"],
        "Rome": ["Seville", "Santorini", "Naples", "Istanbul"],
        "Istanbul": ["Naples", "Rome"],
        "Naples": ["Istanbul", "Santorini", "Rome"],
        "Santorini": ["Rome", "Naples"]
    }
    
    # Build itinerary day by day
    itinerary = []
    day = 1
    
    # Phase 1: Seville
    seville_days = cities["Seville"]
    itinerary.append({"day_range": f"Day {day}-{day + seville_days - 1}", "place": "Seville"})
    day += seville_days - 1  # last day in Seville is also travel day to Rome
    
    # Travel to Rome on last Seville day
    # Day 'day' is in both Seville and Rome
    # Phase 2: Rome
    rome_start_day = day
    rome_days_needed = cities["Rome"] - 1  # because 1 day already counted from travel
    day += 1
    rome_end_day = rome_start_day + rome_days_needed
    itinerary.append({"day_range": f"Day {rome_start_day}-{rome_end_day}", "place": "Rome"})
    day = rome_end_day
    
    # Travel to Istanbul on last Rome day
    # Day 'day' is in both Rome and Istanbul
    # Phase 3: Istanbul
    istanbul_start_day = day
    istanbul_days_needed = cities["Istanbul"] - 1  # 1 day already from travel
    day += 1
    istanbul_end_day = istanbul_start_day + istanbul_days_needed
    itinerary.append({"day_range": f"Day {istanbul_start_day}-{istanbul_end_day}", "place": "Istanbul"})
    day = istanbul_end_day
    
    # Travel to Naples on last Istanbul day
    # Day 'day' is in both Istanbul and Naples
    # Phase 4: Naples
    naples_start_day = day
    naples_days_needed = cities["Naples"] - 1  # 1 day already from travel
    day += 1
    naples_end_day = naples_start_day + naples_days_needed
    itinerary.append({"day_range": f"Day {naples_start_day}-{naples_end_day}", "place": "Naples"})
    day = naples_end_day
    
    # Travel to Santorini on last Naples day
    # Day 'day' is in both Naples and Santorini
    # Phase 5: Santorini
    santorini_start_day = day
    santorini_days_needed = cities["Santorini"] - 1  # 1 day already from travel
    day += 1
    santorini_end_day = santorini_start_day + santorini_days_needed
    itinerary.append({"day_range": f"Day {santorini_start_day}-{santorini_end_day}", "place": "Santorini"})
    
    # Verify constraints
    # Istanbul on days 6-7
    istanbul_days = []
    for entry in itinerary:
        if entry["place"] == "Istanbul":
            start, end = map(int, entry["day_range"].replace("Day ", "").split("-"))
            istanbul_days.extend(range(start, end + 1))
    if not (6 in istanbul_days and 7 in istanbul_days):
        raise ValueError("Istanbul not on days 6-7")
    
    # Santorini on days 13-16
    santorini_days = []
    for entry in itinerary:
        if entry["place"] == "Santorini":
            start, end = map(int, entry["day_range"].replace("Day ", "").split("-"))
            santorini_days.extend(range(start, end + 1))
    if not all(d in santorini_days for d in range(13, 17)):
        raise ValueError("Santorini not on days 13-16")
    
    # Verify total days
    total_itinerary_days = set()
    for entry in itinerary:
        start, end = map(int, entry["day_range"].replace("Day ", "").split("-"))
        total_itinerary_days.update(range(start, end + 1))
    if min(total_itinerary_days) != 1 or max(total_itinerary_days) != total_days:
        raise ValueError(f"Total days mismatch: {min(total_itinerary_days)} to {max(total_itinerary_days)}")
    
    # Verify city days counts
    city_counts = {}
    for entry in itinerary:
        start, end = map(int, entry["day_range"].replace("Day ", "").split("-"))
        city_counts[entry["place"]] = city_counts.get(entry["place"], 0) + (end - start + 1)
    for city, need in cities.items():
        if city_counts.get(city, 0) != need:
            raise ValueError(f"{city} has {city_counts.get(city,0)} days, need {need}")
    
    # Verify flight connections
    for i in range(len(itinerary) - 1):
        city1 = itinerary[i]["place"]
        city2 = itinerary[i + 1]["place"]
        if city2 not in flights[city1]:
            raise ValueError(f"No direct flight from {city1} to {city2}")
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_itinerary()
    print(json.dumps(result, indent=2))