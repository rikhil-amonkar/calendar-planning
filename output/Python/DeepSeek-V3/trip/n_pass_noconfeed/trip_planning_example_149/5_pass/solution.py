import json

def plan_trip():
    # Input parameters
    total_days = 10
    london_days = 3
    santorini_days = 6
    istanbul_days = 3
    conference_days = [5, 10]
    
    # Direct flights
    direct_flights = {
        "Istanbul": ["London"],
        "London": ["Istanbul", "Santorini"],
        "Santorini": ["London"]
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Revised plan:
    # 1. Start in Istanbul (days 1-3)
    # 2. Fly to Santorini (day 4)
    # 3. Stay in Santorini (days 4-9) to cover both conference days
    # 4. Fly to London (day 10)
    # 5. Stay in London (day 10)
    
    # Day 1-3: Istanbul
    itinerary.extend([{"day": day, "location": "Istanbul"} for day in range(1, 4)])
    
    # Day 4: Travel to Santorini
    itinerary.append({"day": 4, "location": "Istanbul", "action": "Fly to Santorini"})
    itinerary.append({"day": 4, "location": "Santorini"})
    
    # Day 5-9: Santorini (covers conference day 5)
    itinerary.extend([{"day": day, "location": "Santorini"} for day in range(5, 10)])
    
    # Day 10: Travel to London (covers conference day 10 in London)
    itinerary.append({"day": 10, "location": "Santorini", "action": "Fly to London"})
    itinerary.append({"day": 10, "location": "London"})
    
    # Verify the counts
    locations = [item["location"] for item in itinerary if "action" not in item]
    london_count = locations.count("London")
    santorini_count = locations.count("Santorini")
    istanbul_count = locations.count("Istanbul")
    
    # Verify conference days (day 5 is in Santorini, day 10 is in London)
    conf_days_ok = True
    for day in conference_days:
        day_ok = False
        for item in itinerary:
            if item["day"] == day and "location" in item and item["location"] in ["Santorini", "London"]:
                day_ok = True
                break
        if not day_ok:
            conf_days_ok = False
            break
    
    if (london_count == london_days and 
        santorini_count == santorini_days and 
        istanbul_count == istanbul_days and 
        conf_days_ok):
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = plan_trip()
print(json.dumps(result, indent=2))