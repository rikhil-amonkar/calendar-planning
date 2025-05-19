import json

def plan_trip():
    cities_order = ["Naples", "Milan", "Seville"]
    city_info = {
        "Naples": {"required_days": 3},
        "Milan": {"required_days": 7},
        "Seville": {"required_days": 4, "fixed_start": 9, "fixed_end": 12}
    }
    direct_flights = {("Naples", "Milan"), ("Milan", "Seville")}
    
    # Check flight connections
    valid = True
    for i in range(len(cities_order)-1):
        a, b = cities_order[i], cities_order[i+1]
        if (a, b) not in direct_flights and (b, a) not in direct_flights:
            valid = False
            break
    if not valid:
        return {"itinerary": []}
    
    itinerary = []
    current_day = 1
    for city in cities_order:
        info = city_info[city]
        if city == "Seville":
            start = info["fixed_start"]
            end = info["fixed_end"]
            if end - start + 1 != info["required_days"]:
                return {"itinerary": []}
        else:
            req_days = info["required_days"]
            start = current_day
            end = start + req_days - 1
            current_day = end + 1  # Next city starts after flight day
        
        day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
        itinerary.append({"day_range": day_range, "place": city})
        if city == "Seville":
            break  # Last city
    
    # Ensure Seville ends on day 12
    if city_info["Seville"]["fixed_end"] != 12:
        return {"itinerary": []}
    
    return {"itinerary": itinerary}

print(json.dumps(plan_trip()))