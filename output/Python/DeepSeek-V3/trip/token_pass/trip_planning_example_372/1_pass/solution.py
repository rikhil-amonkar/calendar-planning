import json

def direct_flight(city1, city2):
    """Check if there's a direct flight between two cities."""
    direct_pairs = [
        ("Porto", "Stuttgart"),
        ("Seville", "Porto"),
        ("Madrid", "Porto"),
        ("Madrid", "Seville")
    ]
    return (city1, city2) in direct_pairs or (city2, city1) in direct_pairs

def is_valid(itinerary, totals_required, conference_days):
    """Check if itinerary satisfies all constraints."""
    if len(itinerary) != 13:
        return False
    
    # Count days per city
    counts = {city: 0 for city in totals_required.keys()}
    for city in itinerary:
        counts[city] += 1
    
    # Check totals match
    for city, required in totals_required.items():
        if counts[city] != required:
            return False
    
    # Check conference days
    for day, city in conference_days:
        if itinerary[day - 1] != city:
            return False
    
    # Check Madrid in first 4 days
    if "Madrid" not in itinerary[:4]:
        return False
    
    # Check travel feasibility
    for i in range(len(itinerary) - 1):
        if itinerary[i] != itinerary[i + 1] and not direct_flight(itinerary[i], itinerary[i + 1]):
            return False
    
    return True

def backtrack(day, itinerary, totals, totals_required, conference_days, city_list):
    """Backtracking search for valid itinerary."""
    if day > 13:
        return itinerary if is_valid(itinerary, totals_required, conference_days) else None
    
    # If this day is fixed by conference
    for conf_day, conf_city in conference_days:
        if day == conf_day:
            if totals[conf_city] >= totals_required[conf_city]:
                return None
            # Check travel from previous day
            if day > 1 and itinerary[day - 2] != conf_city and not direct_flight(itinerary[day - 2], conf_city):
                return None
            itinerary.append(conf_city)
            totals[conf_city] += 1
            res = backtrack(day + 1, itinerary, totals, totals_required, conference_days, city_list)
            if res is not None:
                return res
            itinerary.pop()
            totals[conf_city] -= 1
            return None
    
    # Try each city
    for city in city_list:
        if totals[city] >= totals_required[city]:
            continue
        # Check travel from previous day
        if day > 1 and itinerary[day - 2] != city and not direct_flight(itinerary[day - 2], city):
            continue
        
        itinerary.append(city)
        totals[city] += 1
        
        res = backtrack(day + 1, itinerary, totals, totals_required, conference_days, city_list)
        if res is not None:
            return res
        
        itinerary.pop()
        totals[city] -= 1
    
    return None

def solve():
    # Required totals
    totals_required = {
        "Seville": 2,
        "Stuttgart": 7,
        "Porto": 3,
        "Madrid": 4
    }
    
    # Conference days: (day, city) 1-based
    conference_days = [(7, "Stuttgart"), (13, "Stuttgart")]
    
    city_list = list(totals_required.keys())
    
    # Start search
    itinerary = []
    totals = {city: 0 for city in city_list}
    
    result = backtrack(1, itinerary, totals, totals_required, conference_days, city_list)
    
    if result is None:
        print("No valid itinerary found")
        return
    
    # Convert to day ranges
    day_ranges = []
    start = 0
    while start < 13:
        end = start
        while end < 13 and result[end] == result[start]:
            end += 1
        day_range_str = f"Day {start + 1}-{end}" if end > start + 1 else f"Day {start + 1}"
        day_ranges.append({"day_range": day_range_str, "place": result[start]})
        start = end
    
    output = {"itinerary": day_ranges}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    solve()