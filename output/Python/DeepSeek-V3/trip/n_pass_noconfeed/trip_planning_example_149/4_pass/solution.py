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
    # 2. Fly to London (day 4)
    # 3. Stay in London (days 4-6)
    # 4. Fly to Santorini (day 7)
    # 5. Stay in Santorini (days 7-10) to cover both conference days
    
    # Day 1-3: Istanbul
    itinerary.extend([{"day": day, "location": "Istanbul"} for day in range(1, 4)])
    
    # Day 4: Travel to London
    itinerary.append({"day": 4, "location": "Istanbul", "action": "Fly to London"})
    itinerary.append({"day": 4, "location": "London"})
    
    # Day 5-6: London
    itinerary.extend([{"day": day, "location": "London"} for day in range(5, 7)])
    
    # Day 7: Travel to Santorini
    itinerary.append({"day": 7, "location": "London", "action": "Fly to Santorini"})
    itinerary.append({"day": 7, "location": "Santorini"})
    
    # Day 8-10: Santorini (covers conference days 5 and 10)
    itinerary.extend([{"day": day, "location": "Santorini"} for day in range(8, 11)])
    
    # Verify the counts
    locations = [item["location"] for item in itinerary if "action" not in item]
    london_count = locations.count("London")
    santorini_count = locations.count("Santorini")
    istanbul_count = locations.count("Istanbul")
    
    # Verify conference days (day 5 is in London, day 10 is in Santorini)
    conf_days_ok = True
    for day in conference_days:
        day_ok = False
        for item in itinerary:
            if item["day"] == day and "location" in item and item["location"] == "Santorini":
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